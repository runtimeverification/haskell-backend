{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Unification.UnifierT
    ( UnifierT (..)
    , throwUnificationOrSubstitutionError
    , lowerExceptT
    , runUnifierT
    , maybeUnifierT
    , substitutionSimplifier
    , unificationMakeAnd
    -- * Re-exports
    , module Kore.Unification.Unify
    ) where

import Control.Applicative
    ( Alternative
    )
import Control.Error
import Control.Monad
    ( MonadPlus
    )
import qualified Control.Monad.Except as Error
import qualified Control.Monad.Morph as Morph
import Control.Monad.Trans.Class
    ( MonadTrans (..)
    )

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
import qualified Kore.Internal.Condition as Condition
    ( topTODO
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Logger
    ( MonadLog (..)
    )
import Kore.Profiler.Data
    ( MonadProfiler
    )
import Kore.Step.Simplification.AndTerms
    ( termUnification
    )
import qualified Kore.Step.Simplification.Condition as ConditionSimplifier
import Kore.Step.Simplification.Simplify
    ( ConditionSimplifier (..)
    , MonadSimplify (..)
    , SimplifierVariable
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Simplification.SubstitutionSimplifier
    ( MakeAnd (..)
    )
import Kore.Unification.Error
import Kore.Unification.SubstitutionSimplifier
    ( substitutionSimplifier
    )
import Kore.Unification.Unify
import SMT
    ( MonadSMT (..)
    )

newtype UnifierT (m :: * -> *) a =
    UnifierT
        { getUnifierT :: BranchT (ExceptT UnificationOrSubstitutionError m) a }
    deriving (Functor, Applicative, Monad, Alternative, MonadPlus)

instance MonadTrans UnifierT where
    lift = UnifierT . lift . lift
    {-# INLINE lift #-}

deriving instance MonadLog m => MonadLog (UnifierT m)

deriving instance MonadSMT m => MonadSMT (UnifierT m)

deriving instance MonadProfiler m => MonadProfiler (UnifierT m)

instance MonadSimplify m => MonadSimplify (UnifierT m) where
    localSimplifierTermLike locally =
        \(UnifierT branchT) ->
            UnifierT
                (BranchT.mapBranchT
                    (Morph.hoist (localSimplifierTermLike locally))
                    branchT
                )
    {-# INLINE localSimplifierTermLike #-}

    localSimplifierAxioms locally =
        \(UnifierT branchT) ->
            UnifierT
                (BranchT.mapBranchT
                    (Morph.hoist (localSimplifierAxioms locally))
                    branchT
                )
    {-# INLINE localSimplifierAxioms #-}

    simplifyCondition sideCondition condition =
        simplifyCondition' sideCondition condition
      where
        ConditionSimplifier simplifyCondition' =
            ConditionSimplifier.create substitutionSimplifier
    {-# INLINE simplifyCondition #-}

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

unificationMakeAnd :: MonadUnify unifier => MakeAnd unifier
unificationMakeAnd =
    MakeAnd { makeAnd }
  where
    makeAnd termLike1 termLike2 condition = do
        unified <- termUnification termLike1 termLike2
        BranchT.alternate
            $ Simplifier.simplifyCondition Condition.topTODO
            $ Pattern.andCondition unified condition
