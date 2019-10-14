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
    ( MonadSimplify (..), SimplifierVariable
    , Simplifier
    , TermSimplifier
    , SimplifierT, runSimplifierT
    , Env (..)
    , runSimplifier
    , runSimplifierBranch
    , evalSimplifier
    ) where

import Control.Monad.Catch
    ( MonadCatch
    , MonadThrow
    )
import Control.Monad.IO.Unlift
    ( MonadUnliftIO
    )
import Control.Monad.Reader
import qualified Data.Map.Strict as Map
import qualified GHC.Stack as GHC

import Branch
import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom
    )
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
import Kore.Logger
import Kore.Profiler.Data
    ( MonadProfiler (profile)
    )
import qualified Kore.Step.Axiom.EvaluationStrategy as Axiom.EvaluationStrategy
import qualified Kore.Step.Axiom.Registry as Axiom.Registry
import qualified Kore.Step.Function.Memo as Memo
import qualified Kore.Step.Simplification.Predicate as Predicate
import qualified Kore.Step.Simplification.Rule as Rule
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import Kore.Step.Simplification.Simplify
import SMT
    ( MonadSMT (..)
    , SmtT (..)
    )

-- * Simplifier

data Env simplifier =
    Env
        { metadataTools       :: !(SmtMetadataTools Attribute.Symbol)
        , simplifierTermLike  :: !TermLikeSimplifier
        , simplifierPredicate :: !(PredicateSimplifier simplifier)
        , simplifierAxioms    :: !BuiltinAndAxiomSimplifierMap
        , memo                :: !(Memo.Self simplifier)
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

type Simplifier = SimplifierT (SmtT IO)

instance MonadTrans SimplifierT where
    lift smt = SimplifierT (lift smt)
    {-# INLINE lift #-}

instance (MonadUnliftIO m, WithLog LogMessage m)
    => WithLog LogMessage (SimplifierT m)
  where
    askLogAction = SimplifierT (hoistLogAction SimplifierT <$> askLogAction)
    {-# INLINE askLogAction #-}

    localLogAction mapping =
        SimplifierT . localLogAction mapping . runSimplifierT
    {-# INLINE localLogAction #-}

instance (MonadProfiler m) => MonadProfiler (SimplifierT m)
  where
    profile event duration =
        SimplifierT (profile event (runSimplifierT duration))
    {-# INLINE profile #-}

instance
    ( MonadUnliftIO m
    , MonadSMT m
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

    simplifyPredicate conditional = do
        PredicateSimplifier simplify <- asks simplifierPredicate
        simplify conditional
    {-# INLINE simplifyPredicate #-}

    askSimplifierAxioms = asks simplifierAxioms
    {-# INLINE askSimplifierAxioms #-}

    localSimplifierAxioms locally =
        local $ \env@Env { simplifierAxioms } ->
            env { simplifierAxioms = locally simplifierAxioms }
    {-# INLINE localSimplifierAxioms #-}

    askMemo = asks memo
    {-# INLINE askMemo #-}

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
runSimplifier
    :: GHC.HasCallStack
    => Env (SimplifierT smt)
    -> SimplifierT smt a
    -> smt a
runSimplifier env simplifier = runReaderT (runSimplifierT simplifier) env

{- | Evaluate a simplifier computation, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

  -}
evalSimplifier
    :: forall smt a
    .  GHC.HasCallStack
    => WithLog LogMessage smt
    => (MonadProfiler smt, MonadSMT smt, MonadUnliftIO smt)
    => VerifiedModule Attribute.Symbol Attribute.Axiom
    -> SimplifierT smt a
    -> smt a
evalSimplifier verifiedModule simplifier = do
    env <- runSimplifier earlyEnv initialize
    runReaderT (runSimplifierT simplifier) env
  where
    earlyEnv =
        Env
            { metadataTools = earlyMetadataTools
            , simplifierTermLike
            , simplifierPredicate
            , simplifierAxioms = earlySimplifierAxioms
            , memo = Memo.forgetful
            }
    -- It's safe to build the MetadataTools using the external
    -- IndexedModule because MetadataTools doesn't retain any
    -- knowledge of the patterns which are internalized.
    earlyMetadataTools = MetadataTools.build verifiedModule
    simplifierTermLike = Simplifier.create
    simplifierPredicate = Predicate.create
    -- Initialize without any builtin or axiom simplifiers.
    earlySimplifierAxioms = Map.empty

    verifiedModule' =
        IndexedModule.mapPatterns
            (Builtin.internalize earlyMetadataTools)
            verifiedModule
    metadataTools = MetadataTools.build verifiedModule'

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
            , simplifierPredicate
            , simplifierAxioms
            , memo
            }
