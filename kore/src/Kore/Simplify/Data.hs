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
    SimplifierT,
    runSimplifierT,
    Env (..),
    runSimplifier,
    runSimplifierBranch,
    evalSimplifier,
    evalSimplifierProofs,

    -- * Re-exports
    MonadSimplify (..),
    InternalVariable,
    MonadProf,
) where

import Control.Monad.Catch (
    MonadCatch,
    MonadMask,
    MonadThrow,
 )
import Control.Monad.Morph qualified as Morph
import Control.Monad.Reader
import Control.Monad.State.Strict
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
import Log
import Logic
import Prelude.Kore
import Pretty qualified
import Prof
import SMT (
    SMT (..),
 )

-- * Simplifier

data Env simplifier = Env
    { metadataTools :: !(SmtMetadataTools Attribute.Symbol)
    , simplifierCondition :: !(ConditionSimplifier simplifier)
    , simplifierAxioms :: !BuiltinAndAxiomSimplifierMap
    , memo :: !(Memo.Self simplifier)
    , injSimplifier :: !InjSimplifier
    , overloadSimplifier :: !OverloadSimplifier
    , simplifierXSwitch :: !SimplifierXSwitch
    }

{- | @Simplifier@ represents a simplification action.

A @Simplifier@ can send constraints to the SMT solver through 'MonadSMT'.

A @Simplifier@ can write to the log through 'HasLog'.
-}
newtype SimplifierT smt a = SimplifierT
    { runSimplifierT :: StateT SimplifierCache (ReaderT (Env (SimplifierT smt)) smt) a
    }
    deriving newtype (Functor, Applicative, Monad, MonadSMT)
    deriving newtype (MonadIO, MonadCatch, MonadThrow, MonadMask)
    deriving newtype (MonadReader (Env (SimplifierT smt)))
    deriving newtype (MonadState SimplifierCache)

type Simplifier = SimplifierT SMT

instance MonadTrans SimplifierT where
    lift smt = SimplifierT ((lift . lift) smt)
    {-# INLINE lift #-}

instance MonadLog log => MonadLog (SimplifierT log) where
    logWhile entry = mapSimplifierT $ logWhile entry

instance (MonadMask prof, MonadProf prof) => MonadProf (SimplifierT prof) where
    traceEvent name = lift (traceEvent name)
    {-# INLINE traceEvent #-}

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

instance
    (MonadSMT m, MonadLog m, MonadMask m, MonadProf m) =>
    MonadSimplify (SimplifierT m)
    where
    askMetadataTools = asks metadataTools
    {-# INLINE askMetadataTools #-}

    simplifyPattern sideCondition patt =
        traceProfSimplify patt (Pattern.makeEvaluate sideCondition patt)
    {-# INLINE simplifyPattern #-}

    simplifyTerm = TermLike.simplify
    {-# INLINE simplifyTerm #-}

    simplifyCondition topCondition conditional = do
        ConditionSimplifier simplify <- asks simplifierCondition
        simplify topCondition conditional
    {-# INLINE simplifyCondition #-}

    askSimplifierAxioms = asks simplifierAxioms
    {-# INLINE askSimplifierAxioms #-}

    localSimplifierAxioms locally =
        local $ \env@Env{simplifierAxioms} ->
            env{simplifierAxioms = locally simplifierAxioms}
    {-# INLINE localSimplifierAxioms #-}

    askMemo = asks memo
    {-# INLINE askMemo #-}

    askInjSimplifier = asks injSimplifier
    {-# INLINE askInjSimplifier #-}

    askOverloadSimplifier = asks overloadSimplifier
    {-# INLINE askOverloadSimplifier #-}

    getCache = get
    {-# INLINE getCache #-}

    putCache = put
    {-# INLINE putCache #-}

    askSimplifierXSwitch = asks simplifierXSwitch
    {-# INLINE askSimplifierXSwitch #-}

-- | Run a simplification, returning the results along all branches.
runSimplifierBranch ::
    Monad smt =>
    Env (SimplifierT smt) ->
    -- | simplifier computation
    LogicT (SimplifierT smt) a ->
    smt [a]
runSimplifierBranch env = runSimplifier env . observeAllT

{- | Run a simplification, returning the result of only one branch.

__Warning__: @runSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.
-}
runSimplifier :: Monad smt => Env (SimplifierT smt) -> SimplifierT smt a -> smt a
runSimplifier env simplifier =
    runReaderT (evalStateT (runSimplifierT simplifier) initCache) env

{- | Evaluate a simplifier computation, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.
-}
evalSimplifier ::
    forall smt a.
    (MonadLog smt, MonadSMT smt, MonadMask smt, MonadProf smt, MonadIO smt) =>
    SimplifierXSwitch ->
    VerifiedModuleSyntax Attribute.Symbol ->
    SortGraph ->
    OverloadGraph ->
    SmtMetadataTools Attribute.Symbol ->
    Map AxiomIdentifier [Equation VariableName] ->
    SimplifierT smt a ->
    smt a
evalSimplifier simplifierXSwitch verifiedModule sortGraph overloadGraph metadataTools rawEquations simplifier = do
    !env <- runSimplifier earlyEnv initialize
    runSimplifier env simplifier
  where
    !earlyEnv =
        {-# SCC "evalSimplifier/earlyEnv" #-}
        Env
            { metadataTools = metadataTools
            , simplifierCondition
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

    initialize :: SimplifierT smt (Env (SimplifierT smt))
    initialize = do
        equations <-
            Equation.simplifyExtractedEquations $
                (Map.map . fmap . Equation.mapVariables $ pure mkEquationVariable) $
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
                , simplifierAxioms
                , memo
                , injSimplifier
                , overloadSimplifier
                , simplifierXSwitch
                }

evalSimplifierProofs ::
    forall smt a.
    (MonadLog smt, MonadSMT smt, MonadMask smt, MonadProf smt, MonadIO smt) =>
    SimplifierXSwitch ->
    VerifiedModule Attribute.Symbol ->
    SimplifierT smt a ->
    smt a
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

mapSimplifierT ::
    forall m b.
    Monad m =>
    (forall a. m a -> m a) ->
    SimplifierT m b ->
    SimplifierT m b
mapSimplifierT f simplifierT =
    SimplifierT . StateT $ \s ->
        Morph.hoist f (runStateT (runSimplifierT simplifierT) s)
