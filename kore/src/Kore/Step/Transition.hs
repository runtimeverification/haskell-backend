{-# LANGUAGE UndecidableInstances #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Step.Transition (
    TransitionT (..),
    Transition,
    runTransitionT,
    runTransition,
    tryTransitionT,
    mapTransitionT,
    scatter,
    addRule,
    addRules,
    mapRules,
    record,
    orElse,
    ifte,

    -- * Re-exports
    Seq,
) where

import Control.Monad.Catch (
    MonadCatch (catch),
    MonadThrow (throwM),
 )
import Control.Monad.Except (
    MonadError (..),
 )
import Control.Monad.Reader
import Control.Monad.Trans.Accum (
    AccumT (..),
    mapAccumT,
    runAccumT,
 )
import qualified Control.Monad.Trans.Accum as Accum
import Data.Functor.Identity (
    Identity,
    runIdentity,
 )
import Data.Sequence (
    Seq,
 )
import qualified Data.Sequence as Seq
import Kore.Step.Simplification.Simplify (
    MonadSimplify (..),
 )
import Log (
    MonadLog (..),
 )
import Logic (
    LogicT,
 )
import qualified Logic
import Prelude.Kore
import SMT (
    MonadSMT (..),
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
newtype TransitionT rule m a = TransitionT
    { getTransitionT :: AccumT (Seq rule) (LogicT m) a
    }
    deriving stock (Typeable)
    deriving newtype (Applicative, Functor, Monad)
    deriving newtype (Alternative, MonadPlus)
    deriving newtype (MonadIO)

type Transition r = TransitionT r Identity

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
    ask = lift ask
    {-# INLINE ask #-}

    local f = TransitionT . Accum.mapAccumT (local f) . getTransitionT
    {-# INLINE local #-}

deriving newtype instance MonadSMT m => MonadSMT (TransitionT rule m)

deriving newtype instance MonadSimplify m => MonadSimplify (TransitionT rule m)

instance MonadThrow m => MonadThrow (TransitionT rule m) where
    throwM = lift . throwM

instance MonadCatch m => MonadCatch (TransitionT rule m) where
    catch action handler =
        lift (catch action' handler') >>= scatter
      where
        action' = runTransitionT action
        handler' e = runTransitionT (handler e)

runTransitionT :: Monad m => TransitionT rule m a -> m [(a, Seq rule)]
runTransitionT (TransitionT edge) = Logic.observeAllT (runAccumT edge mempty)

runTransition :: Transition rule a -> [(a, Seq rule)]
runTransition = runIdentity . runTransitionT

tryTransitionT ::
    Monad m =>
    TransitionT rule m a ->
    TransitionT rule' m [(a, Seq rule)]
tryTransitionT = lift . runTransitionT

mapTransitionT ::
    (Monad m, Monad n) =>
    (forall x. m x -> n x) ->
    TransitionT rule m a ->
    TransitionT rule n a
mapTransitionT mapping =
    TransitionT . mapAccumT (Logic.mapLogicT mapping) . getTransitionT

scatter :: [(a, Seq rule)] -> TransitionT rule m a
scatter edges = do
    (a, rules) <- TransitionT (lift (Logic.scatter edges))
    addRules rules
    return a

-- | Record the application of a sequence of rules.
addRules ::
    Foldable f =>
    -- | Sequence of applied rules
    f rule ->
    TransitionT rule m ()
addRules = TransitionT . Accum.add . Seq.fromList . toList

-- | Record the application of a single rule.
addRule :: rule -> TransitionT rule m ()
addRule = TransitionT . Accum.add . Seq.singleton

mapRules ::
    Monad m =>
    (rule -> rule') ->
    TransitionT rule m a ->
    TransitionT rule' m a
mapRules f trans = do
    results <- tryTransitionT trans
    let results' = map (fmap (fmap f)) results
    scatter results'

-- | Get the record of applied rules during an action.
record :: TransitionT rule m a -> TransitionT rule m (a, Seq rule)
record action = TransitionT $
    AccumT $ \w -> do
        (a, rules) <- runAccumT (getTransitionT action) mempty
        return ((a, rules), w <> rules)

{- |

If the first branch returns /any/ values, return /all/ such values; otherwise,
proceed down the second branch. In pseudo-Haskell:

@
orElse first second
  | first /= empty = first
  | otherwise      = second
@

See also: 'ifte'
-}
orElse ::
    Monad m =>
    TransitionT rule m a ->
    TransitionT rule m a ->
    TransitionT rule m a
orElse first = ifte first return -- 'return' is the unit of '>>='

{- |

If the conditional returns /any/ values, send /all/ such values down the "then"
branch; otherwise, proceed down the "else" branch. In pseudo-Haskell:

@
ifte cond thenBranch elseBranch
  | cond /= empty = cond >>= thenBranch
  | otherwise     = elseBranch
@
-}
ifte ::
    Monad m =>
    TransitionT rule m a ->
    (a -> TransitionT rule m b) ->
    TransitionT rule m b ->
    TransitionT rule m b
ifte p t e = TransitionT $
    AccumT $ \w0 ->
        Logic.ifte
            (toLogicT w0 p)
            ( \(a, w1) -> do
                (b, w2) <- toLogicT w1 (t a)
                pure (b, w1 <> w2)
            )
            (toLogicT w0 e)
  where
    toLogicT w = flip runAccumT w . getTransitionT
