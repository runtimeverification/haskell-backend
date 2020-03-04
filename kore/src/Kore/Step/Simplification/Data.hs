{-|
Module      : Kore.Step.Simplification.Data
Description : Data structures used for term simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Step.Simplification.Data
    ( MonadSimplify (..), InternalVariable
    , Simplifier
    , TermSimplifier
    , SimplifierT, runSimplifierT
    , Env (..)
    , runSimplifier
    , runSimplifierBranch
    , evalSimplifier
    ) where

import Prelude.Kore

import Control.Monad.Catch
    ( MonadCatch
    , MonadThrow
    )
import qualified Control.Monad.Morph as Morph
import Control.Monad.Reader
import qualified Data.Map.Strict as Map

import Branch
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin as Builtin
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import qualified Kore.IndexedModule.SortGraph as SortGraph
import Kore.Profiler.Data
    ( MonadProfiler (profile)
    )
import qualified Kore.Step.Axiom.EvaluationStrategy as Axiom.EvaluationStrategy
import qualified Kore.Step.Axiom.Registry as Axiom.Registry
import qualified Kore.Step.Function.Memo as Memo
import qualified Kore.Step.Simplification.Condition as Condition
import Kore.Step.Simplification.InjSimplifier
import Kore.Step.Simplification.OverloadSimplifier
import qualified Kore.Step.Simplification.Rule as Rule
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.SubstitutionSimplifier as SubstitutionSimplifier
import Log
import SMT
    ( MonadSMT (..)
    , SMT (..)
    )

-- * Simplifier

data Env simplifier =
    Env
        { metadataTools       :: !(SmtMetadataTools Attribute.Symbol)
        , simplifierTermLike  :: !TermLikeSimplifier
        , simplifierCondition :: !(ConditionSimplifier simplifier)
        , simplifierAxioms    :: !BuiltinAndAxiomSimplifierMap
        , memo                :: !(Memo.Self simplifier)
        , injSimplifier       :: !InjSimplifier
        , overloadSimplifier  :: !OverloadSimplifier
        }

{- | @Simplifier@ represents a simplification action.

A @Simplifier@ can send constraints to the SMT solver through 'MonadSMT'.

A @Simplifier@ can write to the log through 'HasLog'.

 -}
newtype SimplifierT smt a = SimplifierT
    { runSimplifierT :: ReaderT (Env (SimplifierT smt)) smt a
    }
    deriving (Functor, Applicative, Monad, MonadSMT)
    deriving (MonadIO, MonadCatch, MonadThrow)
    deriving (MonadReader (Env (SimplifierT smt)))

type Simplifier = SimplifierT SMT

instance MonadTrans SimplifierT where
    lift smt = SimplifierT (lift smt)
    {-# INLINE lift #-}

instance Morph.MFunctor SimplifierT where
    hoist f simplifierT = undefined
        -- Morph.hoist f (runSimplifierT simplifierT)

instance MonadLog log => MonadLog (SimplifierT log)

instance (MonadProfiler m) => MonadProfiler (SimplifierT m) where
    profile event duration =
        SimplifierT (profile event (runSimplifierT duration))
    {-# INLINE profile #-}

instance
    ( MonadSMT m
    , MonadProfiler m
    , WithLog LogMessage m
    )
    => MonadSimplify (SimplifierT m)
  where
    askMetadataTools = asks metadataTools
    {-# INLINE askMetadataTools #-}

    askSimplifierTermLike = asks simplifierTermLike
    {-# INLINE askSimplifierTermLike #-}

    localSimplifierTermLike locally =
        local $ \env@Env { simplifierTermLike } ->
            env { simplifierTermLike = locally simplifierTermLike }
    {-# INLINE localSimplifierTermLike #-}

    simplifyCondition topCondition conditional = do
        ConditionSimplifier simplify <- asks simplifierCondition
        simplify topCondition conditional
    {-# INLINE simplifyCondition #-}

    askSimplifierAxioms = asks simplifierAxioms
    {-# INLINE askSimplifierAxioms #-}

    localSimplifierAxioms locally =
        local $ \env@Env { simplifierAxioms } ->
            env { simplifierAxioms = locally simplifierAxioms }
    {-# INLINE localSimplifierAxioms #-}

    askMemo = asks memo
    {-# INLINE askMemo #-}

    askInjSimplifier = asks injSimplifier
    {-# INLINE askInjSimplifier #-}

    askOverloadSimplifier = asks overloadSimplifier
    {-# INLINE askOverloadSimplifier #-}

{- | Run a simplification, returning the results along all branches.
 -}
runSimplifierBranch
    :: Monad smt
    => Env (SimplifierT smt)
    -> BranchT (SimplifierT smt) a
    -- ^ simplifier computation
    -> smt [a]
runSimplifierBranch env = runSimplifier env . gather

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
evalSimplifier
    :: forall smt a
    .  WithLog LogMessage smt
    => (MonadProfiler smt, MonadSMT smt, MonadIO smt)
    => VerifiedModule Attribute.Symbol
    -> SimplifierT smt a
    -> smt a
evalSimplifier verifiedModule simplifier = do
    !env <- runSimplifier earlyEnv initialize
    runReaderT (runSimplifierT simplifier) env
  where
    !earlyEnv =
        Env
            { metadataTools = earlyMetadataTools
            , simplifierTermLike
            , simplifierCondition
            , simplifierAxioms = earlySimplifierAxioms
            , memo = Memo.forgetful
            , injSimplifier
            , overloadSimplifier
            }
    sortGraph = SortGraph.fromIndexedModule verifiedModule
    injSimplifier = mkInjSimplifier sortGraph
    -- It's safe to build the MetadataTools using the external
    -- IndexedModule because MetadataTools doesn't retain any
    -- knowledge of the patterns which are internalized.
    earlyMetadataTools = MetadataTools.build verifiedModule
    simplifierTermLike = Simplifier.create
    substitutionSimplifier = SubstitutionSimplifier.substitutionSimplifier
    simplifierCondition = Condition.create substitutionSimplifier
    -- Initialize without any builtin or axiom simplifiers.
    earlySimplifierAxioms = Map.empty

    verifiedModule' =
        IndexedModule.mapPatterns
            (Builtin.internalize earlyMetadataTools)
            verifiedModule
    metadataTools = MetadataTools.build verifiedModule'
    overloadGraph = OverloadGraph.fromIndexedModule verifiedModule
    overloadSimplifier = mkOverloadSimplifier overloadGraph injSimplifier

    initialize :: SimplifierT smt (Env (SimplifierT smt))
    initialize = do
        let equalityAxioms =
                Axiom.Registry.extractEqualityAxioms verifiedModule'
        functionAxioms <- Rule.simplifyFunctionAxioms equalityAxioms
        let
            builtinEvaluators, userEvaluators, simplifierAxioms
                :: BuiltinAndAxiomSimplifierMap
            builtinEvaluators =
                Axiom.EvaluationStrategy.builtinEvaluation
                <$> Builtin.koreEvaluators verifiedModule'
            userEvaluators =
                Axiom.Registry.axiomPatternsToEvaluators functionAxioms
            simplifierAxioms =
                Map.unionWith
                    Axiom.EvaluationStrategy.simplifierWithFallback
                    builtinEvaluators
                    userEvaluators
        memo <- Memo.new
        return Env
            { metadataTools
            , simplifierTermLike
            , simplifierCondition
            , simplifierAxioms
            , memo
            , injSimplifier
            , overloadSimplifier
            }
