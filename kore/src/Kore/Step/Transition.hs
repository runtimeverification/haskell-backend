{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE UndecidableInstances #-}

module Kore.Step.Transition
    ( TransitionT (..)
    , runTransitionT
    , tryTransitionT
    , mapTransitionT
    , scatter
    , addRule
    , addRules
    , mapRules
    , orElse
    -- * Re-exports
    , Seq
    ) where

import Prelude.Kore

import Control.Monad.Catch
    ( MonadCatch (catch)
    , MonadThrow (throwM)
    )
import Control.Monad.Except
    ( MonadError (..)
    )
import Control.Monad.Reader
import Control.Monad.Trans.Accum
import qualified Control.Monad.Trans.Accum as Accum
import qualified Data.Foldable as Foldable
import Data.Sequence
    ( Seq
    )
import qualified Data.Sequence as Seq
import Data.Typeable
    ( Typeable
    )

import Kore.Profiler.Data
    ( MonadProfiler
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify (..)
    )
import ListT
    ( ListT
    , mapListT
    )
import qualified ListT
import Log
    ( MonadLog (..)
    )
import SMT
    ( MonadSMT (..)
    )

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
    TransitionT { getTransitionT :: AccumT (Seq rule) (ListT m) a }
    deriving
        ( Alternative
        , Applicative
        , Functor
        , Monad
        , MonadIO
        , MonadPlus
        , Typeable
        )

instance MonadLog m => MonadLog (TransitionT rule m) where
    logWhile entry = mapTransitionT $ logWhile entry

instance MonadTrans (TransitionT rule) where
    lift = TransitionT . lift . lift
    {-# INLINE lift #-}

instance MonadError e m => MonadError e (TransitionT rule m) where
    throwError = lift . throwError
    {-# INLINE throwError #-}

    catchError action handler =
        lift (catchError action' handler') >>= scatter
      where
        action' = runTransitionT action
        handler' e = runTransitionT (handler e)
    {-# INLINE catchError #-}

instance MonadReader e m => MonadReader e (TransitionT rule m) where
    ask     = lift ask
    {-# INLINE ask #-}

    local f = TransitionT . Accum.mapAccumT (local f) . getTransitionT
    {-# INLINE local #-}

deriving instance MonadSMT m => MonadSMT (TransitionT rule m)

deriving instance MonadProfiler m => MonadProfiler (TransitionT rule m)

deriving instance MonadSimplify m => MonadSimplify (TransitionT rule m)

instance MonadThrow m => MonadThrow (TransitionT rule m) where
    throwM = lift . throwM

instance MonadCatch m => MonadCatch (TransitionT rule m) where
    catch action handler =
        lift (catch action' handler') >>= scatter
      where
        action' = runTransitionT action
        handler' e = runTransitionT (handler e)

runTransitionT :: Monad m => TransitionT rule m a -> m [(a, Seq rule)]
runTransitionT (TransitionT edge) = ListT.gather (runAccumT edge mempty)

tryTransitionT
    :: Monad m
    => TransitionT rule m a
    -> TransitionT rule' m [(a, Seq rule)]
tryTransitionT = lift . runTransitionT

mapTransitionT
    :: Monad m
    => (forall x. m x -> m x)
    -> TransitionT rule m a
    -> TransitionT rule m a
mapTransitionT mapping =
    TransitionT . mapAccumT (mapListT mapping) . getTransitionT

scatter :: [(a, Seq rule)] -> TransitionT rule m a
scatter edges = do
    (a, rules) <- TransitionT (lift (ListT.scatter edges))
    addRules rules
    return a

{- | Record the application of a sequence of rules.
 -}
addRules
    :: Foldable f
    => f rule
    -- ^ Sequence of applied rules
    -> TransitionT rule m ()
addRules = TransitionT . Accum.add . Seq.fromList . Foldable.toList

{- | Record the application of a single rule.
 -}
addRule :: rule -> TransitionT rule m ()
addRule = TransitionT . Accum.add . Seq.singleton

mapRules
    :: Monad m
    => (rule -> rule')
    -> TransitionT rule m a
    -> TransitionT rule' m a
mapRules f trans = do
    results <- tryTransitionT trans
    let results' = map (fmap (fmap f)) results
    scatter results'

orElse
    :: Monad m
    => TransitionT rule m a
    -> TransitionT rule m a
    -> TransitionT rule m a
orElse first second = do
    results <- tryTransitionT first
    if null results then second else scatter results
