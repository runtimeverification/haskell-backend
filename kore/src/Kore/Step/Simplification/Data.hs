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
    ( MonadSimplify (..)
    , Simplifier
    , TermSimplifier
    , SimplifierT, runSimplifierT
    , Env (..)
    , runSimplifier
    , evalSimplifier
    , SimplificationType (..)
    -- * Branching
    , BranchT
    , mapBranchT
    , evalSimplifierBranch
    , gather
    , gatherAll
    , scatter
    , foldBranchT
    , alternate
    ) where

import           Control.Monad.Catch
                 ( MonadCatch, MonadThrow )
import           Control.Monad.IO.Unlift
                 ( MonadUnliftIO )
import           Control.Monad.Reader
import qualified GHC.Stack as GHC

import           Branch
import qualified Kore.Attribute.Symbol as Attribute
                 ( Symbol )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Logger
import           Kore.Profiler.Data
                 ( MonadProfiler (profileDuration) )
import           Kore.Step.Simplification.Simplify
import           SMT
                 ( MonadSMT (..), SMT, SmtT (..) )

{-| 'And' simplification is very similar to 'Equals' simplification.
This type is used to distinguish between the two in the common code.
-}
data SimplificationType = And | Equals

-- * Simplifier

data Env =
    Env
        { metadataTools       :: !(SmtMetadataTools Attribute.Symbol)
        , simplifierTermLike  :: !TermLikeSimplifier
        , simplifierPredicate :: !PredicateSimplifier
        , simplifierAxioms    :: !BuiltinAndAxiomSimplifierMap
        }

{- | @Simplifier@ represents a simplification action.

A @Simplifier@ can send constraints to the SMT solver through 'MonadSMT'.

A @Simplifier@ can write to the log through 'HasLog'.

 -}
newtype SimplifierT m a = SimplifierT
    { runSimplifierT :: ReaderT Env m a
    }
    deriving (Functor, Applicative, Monad, MonadSMT)
    deriving (MonadIO, MonadCatch, MonadThrow, MonadTrans)
    deriving (MonadReader Env)

type Simplifier = SimplifierT (SmtT IO)

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
    profileDuration event duration =
        SimplifierT (profileDuration event (runSimplifierT duration))
    {-# INLINE profileDuration #-}

instance (MonadUnliftIO m, MonadSMT m, WithLog LogMessage m, MonadProfiler m)
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

    askSimplifierPredicate = asks simplifierPredicate
    {-# INLINE askSimplifierPredicate #-}

    localSimplifierPredicate locally =
        local $ \env@Env { simplifierPredicate } ->
            env { simplifierPredicate = locally simplifierPredicate }
    {-# INLINE localSimplifierPredicate #-}

    askSimplifierAxioms = asks simplifierAxioms
    {-# INLINE askSimplifierAxioms #-}

    localSimplifierAxioms locally =
        local $ \env@Env { simplifierAxioms } ->
            env { simplifierAxioms = locally simplifierAxioms }
    {-# INLINE localSimplifierAxioms #-}

{- | Run a simplification, returning the results along all branches.
 -}
evalSimplifierBranch
    :: Env
    -> BranchT Simplifier a
    -- ^ simplifier computation
    -> SMT [a]
evalSimplifierBranch env = evalSimplifier env . gather

{- | Run a simplification, returning the result of only one branch.

__Warning__: @runSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

 -}
runSimplifier
    :: GHC.HasCallStack
    => Env
    -> Simplifier a
    -- ^ simplifier computation
    -> SMT a
runSimplifier env = evalSimplifier env

{- | Evaluate a simplifier computation, returning the result of only one branch.

__Warning__: @evalSimplifier@ calls 'error' if the 'Simplifier' does not contain
exactly one branch. Use 'evalSimplifierBranch' to evaluation simplifications
that may branch.

  -}
evalSimplifier
    :: GHC.HasCallStack
    => Env
    -> SimplifierT smt a
    -> smt a
evalSimplifier env = flip runReaderT env . runSimplifierT
