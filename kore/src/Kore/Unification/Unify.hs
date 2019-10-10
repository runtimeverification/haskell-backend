{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Unification.Unify
    ( MonadUnify (..), SimplifierVariable
    , UnifierT (..)
    , throwUnificationOrSubstitutionError
    , lowerExceptT
    , runUnifierT
    , maybeUnifierT
    ) where

import Control.Applicative
    ( Alternative
    , empty
    )
import Control.Error
import Control.Monad
    ( MonadPlus
    )
import qualified Control.Monad.Except as Error
import Control.Monad.Trans.Class
    ( MonadTrans (..)
    )
import Data.Text.Prettyprint.Doc
    ( Doc
    )

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
import Kore.Internal.TermLike
    ( SortedVariable
    , TermLike
    )
import Kore.Logger
    ( LogMessage
    , WithLog (..)
    )
import Kore.Profiler.Data
    ( MonadProfiler
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify (..)
    , SimplifierVariable
    )
import Kore.Unification.Error
import Kore.Unparser
    ( Unparse
    )
import SMT
    ( MonadSMT (..)
    )

-- | @MonadUnify@ is used throughout the step and unification modules. Its main
-- goal is to abstract over an 'ExceptT' over a 'UnificationOrSubstitutionError'
-- running in a 'Simplifier' monad.
--
-- 'MonadUnify' chooses its error/left type to 'UnificationOrSubstitutionError'
-- and provides functions to throw these errors. The point of this is to be able
-- to display information about unification failures through 'explainFailure'.
class (Alternative unifier, MonadSimplify unifier) => MonadUnify unifier where
    throwSubstitutionError
        :: SubstitutionError
        -> unifier a
    default throwSubstitutionError
        :: (MonadTrans t, MonadUnify m, unifier ~ t m)
        => SubstitutionError -> unifier a
    throwSubstitutionError = lift . throwSubstitutionError
    {-# INLINE throwSubstitutionError #-}

    throwUnificationError
        :: UnificationError
        -> unifier a
    default throwUnificationError
        :: (MonadTrans t, MonadUnify m, unifier ~ t m)
        => UnificationError -> unifier a
    throwUnificationError = lift . throwUnificationError
    {-# INLINE throwUnificationError #-}

    -- TODO: This is ugly and not type-safe
    gather :: unifier a -> unifier [a]

    scatter :: Traversable t => t a -> unifier a

    explainBottom
        :: (SortedVariable variable, Unparse variable)
        => Doc ()
        -> TermLike variable
        -> TermLike variable
        -> unifier ()
    explainBottom _ _ _ = pure ()

    explainAndReturnBottom
        :: (SortedVariable variable, Unparse variable)
        => Doc ()
        -> TermLike variable
        -> TermLike variable
        -> unifier a
    explainAndReturnBottom message first second = do
        explainBottom message first second
        empty

newtype UnifierT (m :: * -> *) a =
    UnifierT
        { getUnifierT :: BranchT (ExceptT UnificationOrSubstitutionError m) a }
    deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

instance MonadTrans UnifierT where
    lift = UnifierT . lift . lift
    {-# INLINE lift #-}

deriving instance WithLog LogMessage m => WithLog LogMessage (UnifierT m)

deriving instance MonadSMT m => MonadSMT (UnifierT m)

deriving instance MonadProfiler m => MonadProfiler (UnifierT m)

deriving instance MonadSimplify m => MonadSimplify (UnifierT m)

instance MonadSimplify m => MonadUnify (UnifierT m) where
    throwSubstitutionError =
        UnifierT
        . lift
        . Error.throwError
        . SubstitutionError
    {-# INLINE throwSubstitutionError #-}

    throwUnificationError =
        UnifierT
        . lift
        . Error.throwError
        . UnificationError
    {-# INLINE throwUnificationError #-}

    gather = UnifierT . lift . BranchT.gather . getUnifierT
    {-# INLINE gather #-}

    scatter = UnifierT . BranchT.scatter
    {-# INLINE scatter #-}

-- | Lower an 'ExceptT UnificationOrSubstitutionError' into a 'MonadUnify'.
lowerExceptT
    :: MonadUnify unifier
    => ExceptT UnificationOrSubstitutionError unifier a
    -> unifier a
lowerExceptT e =
    runExceptT e >>= either throwUnificationOrSubstitutionError pure

throwUnificationOrSubstitutionError
    :: MonadUnify unifier
    => UnificationOrSubstitutionError
    -> unifier a
throwUnificationOrSubstitutionError (SubstitutionError s) =
    throwSubstitutionError s
throwUnificationOrSubstitutionError (UnificationError u) =
    throwUnificationError u

runUnifierT
    :: MonadSimplify m
    => UnifierT m a
    -> m (Either UnificationOrSubstitutionError [a])
runUnifierT = runExceptT . BranchT.gather . getUnifierT

{- | Run a 'Unifier', returning 'Nothing' upon error.
 -}
maybeUnifierT :: MonadSimplify m => UnifierT m a -> MaybeT m [a]
maybeUnifierT = hushT . BranchT.gather . getUnifierT
