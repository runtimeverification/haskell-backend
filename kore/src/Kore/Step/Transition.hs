{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Step.Transition
    ( TransitionT (..)
    , runTransitionT
    , tryTransitionT
    , scatter
    , addRule
    , addRules
    ) where

import           Control.Applicative
import qualified Control.Monad.Morph as Monad.Morph
import           Control.Monad.Reader
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Accum
                 ( AccumT, runAccumT )
import qualified Control.Monad.Trans.Accum as Accum
import qualified Data.Foldable as Foldable
import           Data.Typeable
                 ( Typeable )

import           ListT
                 ( ListT )
import qualified ListT
import           SMT
                 ( MonadSMT, liftSMT )

{- | @TransitionT@ represents a transition between program states.

During the transition, a sequence of @rule@s may be applied; @TransitionT@
collects this sequence for the purpose of labeling the edges of the execution
graph. Use 'addRule' or 'addRules' to record the application of a rule or rules.

Use 'Alternative' to represent branching transitions, i.e. transitions from one
parent to many children. The sequence of rules leading to each child will
contain all the rules recorded before the branch, but each child keeps a
separate record of applied rules after the branch.

 -}
newtype TransitionT rule m a =
    TransitionT { getTransitionT :: AccumT [rule] (ListT m) a }
    deriving
        ( Alternative
        , Applicative
        , Functor
        , Monad
        , MonadIO
        , MonadPlus
        , Typeable
        )

instance MonadTrans (TransitionT rule) where
    lift = TransitionT . Monad.Trans.lift . Monad.Trans.lift

instance MonadSMT m => MonadSMT (TransitionT rule m) where
    liftSMT = lift . liftSMT
    {-# INLINE liftSMT #-}

runTransitionT :: Monad m => TransitionT rule m a -> m [(a, [rule])]
runTransitionT (TransitionT edge) = ListT.gather (runAccumT edge [])

tryTransitionT
    :: Monad m
    => TransitionT rule m a
    -> TransitionT rule m [(a, [rule])]
tryTransitionT = Monad.Trans.lift . runTransitionT

scatter :: [(a, [rule])] -> TransitionT rule m a
scatter edges = do
    (a, rules) <- TransitionT (Monad.Trans.lift (ListT.scatter edges))
    addRules rules
    return a

{- | Record the application of a sequence of rules.
 -}
addRules
    :: Foldable f
    => f rule
    -- ^ Sequence of applied rules
    -> TransitionT rule m ()
addRules = TransitionT . Accum.add . Foldable.toList

{- | Record the application of a single rule.
 -}
addRule :: rule -> TransitionT rule m ()
addRule = TransitionT . Accum.add . (: [])
