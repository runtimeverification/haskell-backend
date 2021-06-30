{-# LANGUAGE UndecidableInstances #-}

{- |
Module      : Kore.Simplify.Data
Description : Data structures used for term simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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
import qualified Control.Monad.Morph as Morph
import Control.Monad.Reader
import qualified Data.Map.Strict as Map
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Builtin as Builtin
import qualified Kore.Equation as Equation
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import qualified Kore.IndexedModule.SortGraph as SortGraph
import Kore.Internal.TermLike (
    TermLike,
 )
import qualified Kore.Rewrite.Axiom.EvaluationStrategy as Axiom.EvaluationStrategy
import Kore.Rewrite.Axiom.Identifier (
    matchAxiomIdentifier,
 )
import Kore.Rewrite.Axiom.Registry (
    mkEvaluatorRegistry,
 )
import qualified Kore.Rewrite.Function.Memo as Memo
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkEquationVariable,
 )
import qualified Kore.Simplify.Condition as Condition
import Kore.Simplify.InjSimplifier
import Kore.Simplify.OverloadSimplifier
import Kore.Simplify.Simplify
import qualified Kore.Simplify.SubstitutionSimplifier as SubstitutionSimplifier
import qualified Kore.Simplify.TermLike as TermLike
import Log
import Logic
import Prelude.Kore
import qualified Pretty
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
    }

{- | @Simplifier@ represents a simplification action.

A @Simplifier@ can send constraints to the SMT solver through 'MonadSMT'.

A @Simplifier@ can write to the log through 'HasLog'.
-}
newtype SimplifierT smt a = SimplifierT
    { runSimplifierT :: ReaderT (Env (SimplifierT smt)) smt a
    }
    deriving newtype (Functor, Applicative, Monad, MonadSMT)
    deriving newtype (MonadIO, MonadCatch, MonadThrow, MonadMask)
    deriving newtype (MonadReader (Env (SimplifierT smt)))

type Simplifier = SimplifierT SMT

instance MonadTrans SimplifierT where
    lift smt = SimplifierT (lift smt)
    {-# INLINE lift #-}

instance MonadLog log => MonadLog (SimplifierT log) where
    logWhile entry = mapSimplifierT $ logWhile entry

instance (MonadMask prof, MonadProf prof) => MonadProf (SimplifierT prof) where
    traceEvent name = lift (traceEvent name)
    {-# INLINE traceEvent #-}

traceProfSimplify ::
    MonadProf prof =>
    TermLike RewritingVariableName ->
    prof a ->
    prof a
traceProfSimplify termLike =
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

    simplifyTermLike sideCondition termLike =
        traceProfSimplify termLike (TermLike.simplify sideCondition termLike)
    {-# INLINE simplifyTermLike #-}

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
runSimplifier :: Env (SimplifierT smt) -> SimplifierT smt a -> smt a
runSimplifier env simplifier = runReaderT (runSimplifierT simplifier) env

{- | Evaluate a simplifier computation, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.
-}
evalSimplifier ::
    forall smt a.
    (MonadLog smt, MonadSMT smt, MonadMask smt, MonadProf smt, MonadIO smt) =>
    VerifiedModule Attribute.Symbol ->
    SimplifierT smt a ->
    smt a
evalSimplifier verifiedModule simplifier = do
    !env <- runSimplifier earlyEnv initialize
    runReaderT (runSimplifierT simplifier) env
  where
    !earlyEnv =
        {-# SCC "evalSimplifier/earlyEnv" #-}
        Env
            { metadataTools = earlyMetadataTools
            , simplifierCondition
            , simplifierAxioms = earlySimplifierAxioms
            , memo = Memo.forgetful
            , injSimplifier
            , overloadSimplifier
            }
    sortGraph =
        {-# SCC "evalSimplifier/sortGraph" #-}
        SortGraph.fromIndexedModule verifiedModule
    injSimplifier =
        {-# SCC "evalSimplifier/injSimplifier" #-}
        mkInjSimplifier sortGraph
    -- It's safe to build the MetadataTools using the external
    -- IndexedModule because MetadataTools doesn't retain any
    -- knowledge of the patterns which are internalized.
    earlyMetadataTools = MetadataTools.build verifiedModule
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
        IndexedModule.mapPatterns
            (Builtin.internalize earlyMetadataTools)
            verifiedModule
    metadataTools =
        {-# SCC "evalSimplifier/metadataTools" #-}
        MetadataTools.build verifiedModule'
    overloadGraph =
        {-# SCC "evalSimplifier/overloadGraph" #-}
        OverloadGraph.fromIndexedModule verifiedModule
    overloadSimplifier =
        {-# SCC "evalSimplifier/overloadSimplifier" #-}
        mkOverloadSimplifier overloadGraph injSimplifier

    initialize :: SimplifierT smt (Env (SimplifierT smt))
    initialize = do
        equations <-
            Equation.simplifyExtractedEquations $
                (Map.map . fmap . Equation.mapVariables $ pure mkEquationVariable) $
                    Equation.extractEquations verifiedModule'
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
                }

mapSimplifierT ::
    forall m b.
    Monad m =>
    (forall a. m a -> m a) ->
    SimplifierT m b ->
    SimplifierT m b
mapSimplifierT f simplifierT =
    SimplifierT $
        Morph.hoist f (runSimplifierT simplifierT)
