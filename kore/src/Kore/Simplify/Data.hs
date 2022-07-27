{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Kore.Simplify.Data
Description : Data structures used for term simplification.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.Data (
    Simplifier,
    TermSimplifier,
    Env (..),
    runSimplifier,
    runSimplifierBranch,
    evalSimplifier,
    evalSimplifierProofs,

    -- * Re-exports
    MonadSimplify (..),
    askMetadataTools,
    simplifyPattern,
    simplifyTerm,
    askSimplifierAxioms,
    askInjSimplifier,
    askOverloadSimplifier,
    getCache,
    putCache,
    askSimplifierXSwitch,
    InternalVariable,
    MonadProf,
) where

import Control.Monad.Reader
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.Builtin qualified as Builtin
import Kore.Equation qualified as Equation
import Kore.Equation.Equation (
    Equation (..),
 )
import Kore.IndexedModule.IndexedModule (
    IndexedModule (..),
    VerifiedModule,
    VerifiedModuleSyntax,
 )
import Kore.IndexedModule.IndexedModule qualified as IndexedModule
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.IndexedModule.MetadataToolsBuilder qualified as MetadataTools
import Kore.IndexedModule.OverloadGraph
import Kore.IndexedModule.OverloadGraph qualified as OverloadGraph
import Kore.IndexedModule.SortGraph
import Kore.IndexedModule.SortGraph qualified as SortGraph
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.Pattern qualified as Pattern
import Kore.Rewrite.Axiom.EvaluationStrategy qualified as Axiom.EvaluationStrategy
import Kore.Rewrite.Axiom.Identifier (
    AxiomIdentifier,
    matchAxiomIdentifier,
 )
import Kore.Rewrite.Axiom.Registry (
    mkEvaluatorRegistry,
 )
import Kore.Rewrite.Function.Memo qualified as Memo
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkEquationVariable,
 )
import Kore.Simplify.Condition qualified as Condition
import Kore.Simplify.InjSimplifier
import Kore.Simplify.OverloadSimplifier
import Kore.Simplify.Pattern qualified as Pattern
import Kore.Simplify.Simplify
import Kore.Simplify.SubstitutionSimplifier qualified as SubstitutionSimplifier
import Kore.Simplify.TermLike qualified as TermLike
import Kore.Syntax.Variable (
    VariableName,
 )
import Logic
import Prelude.Kore
import Pretty qualified
import Prof
import SMT (
    SMT,
 )

traceProfSimplify ::
    MonadProf prof =>
    Pattern RewritingVariableName ->
    prof a ->
    prof a
traceProfSimplify (Pattern.toTermLike -> termLike) =
    maybe id traceProf ident
  where
    ident =
        (":simplify:" <>)
            . Pretty.renderText
            . Pretty.layoutOneLine
            . Pretty.pretty
            <$> matchAxiomIdentifier termLike

-- | Run a simplification, returning the results along all branches.
runSimplifierBranch ::
    Env ->
    -- | simplifier computation
    LogicT Simplifier a ->
    SMT [a]
runSimplifierBranch env = runSimplifier env . observeAllT

mkSimplifierEnv ::
    SimplifierXSwitch ->
    VerifiedModuleSyntax Attribute.Symbol ->
    SortGraph ->
    OverloadGraph ->
    SmtMetadataTools Attribute.Symbol ->
    Map AxiomIdentifier [Equation VariableName] ->
    SMT Env
mkSimplifierEnv simplifierXSwitch verifiedModule sortGraph overloadGraph metadataTools rawEquations =
    runSimplifier earlyEnv initialize
  where
    !earlyEnv =
        {-# SCC "evalSimplifier/earlyEnv" #-}
        Env
            { metadataTools = metadataTools
            , simplifierCondition
            , simplifierPattern
            , simplifierTerm
            , simplifierAxioms = earlySimplifierAxioms
            , memo = Memo.forgetful
            , injSimplifier
            , overloadSimplifier
            , simplifierXSwitch
            }
    injSimplifier =
        {-# SCC "evalSimplifier/injSimplifier" #-}
        mkInjSimplifier sortGraph
    substitutionSimplifier =
        {-# SCC "evalSimplifier/substitutionSimplifier" #-}
        SubstitutionSimplifier.substitutionSimplifier
    simplifierCondition =
        {-# SCC "evalSimplifier/simplifierCondition" #-}
        Condition.create substitutionSimplifier
    simplifierPattern sideCondition patt =
        {-# SCC "evalSimplifier/simplifierPattern" #-}
        traceProfSimplify patt (Pattern.makeEvaluate sideCondition patt)
    simplifierTerm =
        {-# SCC "evalSimplifier/simplifierTerm" #-}
        TermLike.simplify
    -- Initialize without any builtin or axiom simplifiers.
    earlySimplifierAxioms = Map.empty

    verifiedModule' =
        {-# SCC "evalSimplifier/verifiedModule'" #-}
        IndexedModule.mapAliasPatterns
            (Builtin.internalize metadataTools)
            verifiedModule
    overloadSimplifier =
        {-# SCC "evalSimplifier/overloadSimplifier" #-}
        mkOverloadSimplifier overloadGraph injSimplifier

    initialize :: Simplifier Env
    initialize = do
        equations <-
            Equation.simplifyExtractedEquations $
                (Map.map . fmap . Equation.mapVariables $ pure mkEquationVariable)
                    rawEquations
        let builtinEvaluators
                , userEvaluators
                , simplifierAxioms ::
                    BuiltinAndAxiomSimplifierMap
            userEvaluators = mkEvaluatorRegistry equations
            builtinEvaluators =
                Axiom.EvaluationStrategy.builtinEvaluation
                    <$> Builtin.koreEvaluators verifiedModule'
            simplifierAxioms =
                {-# SCC "evalSimplifier/simplifierAxioms" #-}
                Map.unionWith
                    Axiom.EvaluationStrategy.simplifierWithFallback
                    builtinEvaluators
                    userEvaluators
        memo <- Memo.new
        return
            Env
                { metadataTools
                , simplifierCondition
                , simplifierPattern
                , simplifierTerm
                , simplifierAxioms
                , memo
                , injSimplifier
                , overloadSimplifier
                , simplifierXSwitch
                }

{- | Evaluate a simplifier computation, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.
-}
evalSimplifier ::
    SimplifierXSwitch ->
    VerifiedModuleSyntax Attribute.Symbol ->
    SortGraph ->
    OverloadGraph ->
    SmtMetadataTools Attribute.Symbol ->
    Map AxiomIdentifier [Equation VariableName] ->
    Simplifier a ->
    SMT a
evalSimplifier simplifierXSwitch verifiedModule sortGraph overloadGraph metadataTools rawEquations simplifier = do
    env <- mkSimplifierEnv simplifierXSwitch verifiedModule sortGraph overloadGraph metadataTools rawEquations
    runSimplifier env simplifier

evalSimplifierProofs ::
    SimplifierXSwitch ->
    VerifiedModule Attribute.Symbol ->
    Simplifier a ->
    SMT a
evalSimplifierProofs simplifierXSwitch verifiedModule simplifier =
    evalSimplifier simplifierXSwitch (indexedModuleSyntax verifiedModule) sortGraph overloadGraph metadataTools rawEquations simplifier
  where
    sortGraph =
        {-# SCC "evalSimplifier/sortGraph" #-}
        SortGraph.fromIndexedModule verifiedModule
    -- It's safe to build the MetadataTools using the external
    -- IndexedModule because MetadataTools doesn't retain any
    -- knowledge of the patterns which are internalized.
    earlyMetadataTools = MetadataTools.build verifiedModule
    verifiedModule' =
        {-# SCC "evalSimplifier/verifiedModule'" #-}
        IndexedModule.mapPatterns
            (Builtin.internalize earlyMetadataTools)
            verifiedModule
    overloadGraph =
        {-# SCC "evalSimplifier/overloadGraph" #-}
        OverloadGraph.fromIndexedModule verifiedModule
    metadataTools = MetadataTools.build verifiedModule'
    rawEquations = Equation.extractEquations verifiedModule'
