{-# LANGUAGE MultiWayIf #-}

{- |
Copyright   : (c) Runtime Verification, 2018-2022
License     : BSD-3-Clause
Maintainer  : jost.berthold@runtimeverification.com
-}
module Kore.Exec.GraphTraversal (
    graphTraversal,
    simpleTransition,
    Step,
    TState (..),
    TransitionResult (..),
    TraversalResult (..),
    transitionWithRule,
) where

import Control.Monad (foldM)
import Control.Monad.Trans.State
import Data.Limit
import Data.List.NonEmpty qualified as NE
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import GHC.Natural
import Kore.Rewrite.Strategy (
    -- FIXME assimilate definitions and remove import
    FinalNodeType (..),
    GraphSearchOrder (..),
    LimitExceeded (..),
    unfoldSearchOrder,
 )
import Kore.Rewrite.Transition (
    TransitionT (..),
    runTransitionT,
 )
import Kore.Simplify.Data (Simplifier)
import Prelude.Kore
import Pretty

data TransitionResult a
    = -- | straight-line execution
      Continuing a
    | -- | branch point (1st arg), branching into 2nd arg elements
      Branch a (NonEmpty a)
    | -- | no next state but not final (e.g., not goal state, or side
      -- conditions do not hold)
      Stuck a
    | -- | final state (e.g., goal state reached, side conditions hold)
      Final a
    | -- | not stuck, but also not final (maximum depth reached before
      -- finishing the proof). Provides the "next" states for the result.
      Stopped [a]
    deriving stock (Eq, Show)

instance Functor TransitionResult where
    fmap f = \case
        Continuing a -> Continuing $ f a
        Branch a as -> Branch (f a) $ NE.map f as
        Stuck a -> Stuck $ f a
        Final a -> Final $ f a
        Stopped as -> Stopped (map f as)

instance Pretty a => Pretty (TransitionResult a) where
    pretty = \case
        Continuing a -> single "Continuing" a
        Branch a as -> multi "Branch" "node" a "successors" (NE.toList as)
        Stuck a -> single "Stuck" a
        Final a -> single "Final" a
        Stopped as ->
            Pretty.vsep $
                "Stopped" : map (Pretty.indent 4 . Pretty.pretty) as
      where
        single :: Doc x -> a -> Doc x
        single lbl a =
            Pretty.vsep [lbl, Pretty.indent 4 $ Pretty.pretty a]

        multi :: Doc x -> Doc x -> a -> Doc x -> [a] -> Doc x
        multi lbl lbl1 a lbl2 as =
            Pretty.vsep $
                [ lbl
                , Pretty.indent 2 $ "- " <> lbl1
                , Pretty.indent 4 $ Pretty.pretty a
                , Pretty.indent 2 $ "- " <> lbl2
                ]
                    <> map (Pretty.indent 4 . Pretty.pretty) as

isStuck, isFinal, isStopped, isBranch :: TransitionResult a -> Bool
isStuck (Stuck _) = True
isStuck _ = False
isFinal (Final _) = True
isFinal _ = False
isStopped (Stopped _) = True
isStopped _ = False
isBranch (Branch _ _) = True
isBranch _ = False

extractNext :: TransitionResult a -> [a]
extractNext = \case
    Continuing a -> [a]
    Branch _ as -> NE.toList as
    Stuck _ -> []
    Final _ -> []
    Stopped as -> as

extractState :: TransitionResult a -> Maybe a
extractState = \case
    Continuing _ -> Nothing
    Branch a _ -> Just a
    Stuck a -> Just a
    Final a -> Just a
    Stopped _ -> Nothing

{- | A sequence of transition instructions executed together as a
 single transition by the transition function.
-}
type Step instr = [instr]

{- | The traversal state, including subsequent steps to take in the
   traversal.
-}
data TState instr config = TState
    { -- | remaining steps available for the traversal
      nextSteps :: [Step instr]
    , -- | current configuration (i.e., claim or program state)
      currentState :: config
    }

----------------------------------------
graphTraversal ::
    forall config instr.
    -- | Whether to stop on branches or not. This could be handled in
    -- the transition function, too, since the algorithm will _always_
    -- stop on 'Stuck', 'Final', and `Stopped`. It is clearer to add
    -- this explicitly here, though.
    FinalNodeType ->
    -- queue updating parameters,
    -- we construct enqueue :: [a] -> Seq a -> m (Either LimitExceeded (Seq a)) from it

    -- | BreadthFirst, DepthFirst
    GraphSearchOrder ->
    -- | breadth limit, essentially a natural number
    Limit Natural ->
    -- | transition function
    ( TState instr config ->
      Simplifier (TransitionResult (TState instr config))
    ) ->
    -- | max-counterexamples, included in the internal logic
    Limit Natural ->
    -- | steps to execute
    [Step instr] ->
    -- | initial state
    config ->
    Simplifier (TraversalResult config)
graphTraversal
    stopOn
    direction
    breadthLimit
    transit
    maxCounterExamples
    steps
    start =
        enqueue [TState steps start] Seq.empty
            >>= either
                (pure . const (GotStuck 0 [start]))
                (\q -> evalStateT (worker q >>= checkLeftUnproven) [])
      where
        enqueue' = unfoldSearchOrder direction

        enqueue ::
            [TState instr config] ->
            Seq (TState instr config) ->
            Simplifier
                ( Either
                    (LimitExceeded (TState instr config))
                    (Seq (TState instr config))
                )
        enqueue as q = do
            newQ <- enqueue' as q
            pure $
                if exceedsLimit newQ
                    then Left (LimitExceeded newQ)
                    else Right newQ

        exceedsLimit :: Seq a -> Bool
        exceedsLimit =
            not . withinLimit breadthLimit . fromIntegral . Seq.length

        shouldStop :: TransitionResult (TState instr config) -> Bool
        shouldStop =
            case stopOn of
                Leaf -> const False
                LeafOrBranching -> isBranch

        worker ::
            Seq (TState instr config) ->
            StateT
                [TransitionResult (TState instr config)]
                Simplifier
                (TraversalResult (TState instr config))
        worker Seq.Empty = Ended . reverse <$> gets (mapMaybe extractState)
        worker (a :<| as) = do
            result <- lift $ step a as
            case result of
                Continue nextQ -> worker nextQ
                Output oneResult nextQ -> do
                    modify (oneResult :)
                    if not (isStuck oneResult)
                        then worker nextQ
                        else do
                            stuck <- gets (filter isStuck)
                            if maxCounterExamples <= Limit (fromIntegral (length stuck))
                                then
                                    pure $
                                        GotStuck (Seq.length nextQ) (mapMaybe extractState stuck)
                                else worker nextQ
                Abort lastState queue -> do
                    pure $ Aborted (Seq.length queue) (extractNext lastState)

        step ::
            (TState instr config) ->
            Seq (TState instr config) ->
            Simplifier (StepResult (TState instr config))
        step a q = do
            next <- transit a
            if (isStuck next || isFinal next || isStopped next || shouldStop next)
                then pure (Output next q)
                else
                    let abort (LimitExceeded queue) = Abort next queue
                     in either abort Continue <$> enqueue (extractNext next) q

        checkLeftUnproven ::
            TraversalResult (TState instr config) ->
            StateT
                [TransitionResult (TState instr config)]
                Simplifier
                (TraversalResult config)
        checkLeftUnproven = \case
            result@(Ended{}) -> do
                collected <- gets reverse
                -- we collect a maximum of 'maxCounterExamples' Stuck states
                let stuck = map (fmap currentState) $ filter isStuck collected
                -- Other states may be unfinished but not stuck (Stopped)
                -- Only provide the requested amount of states (maxCounterExamples)
                let unproven =
                        takeWithin maxCounterExamples . map (fmap currentState) $
                            filter isStopped collected
                pure $
                    if
                            | (not $ null stuck) ->
                                GotStuck 0 (mapMaybe extractState stuck)
                            | not $ null unproven ->
                                GotStuck 0 (concatMap extractNext unproven)
                            | otherwise -> fmap currentState result
            other -> pure $ fmap currentState other

data StepResult a
    = -- | Traversal continues with given queue.
      Continue (Seq a)
    | -- | Traversal produced a result and continues with given queue.
      -- Typically a final or stuck state (or a "stop" state), and the
      -- queue is the remaining work.
      Output (TransitionResult a) (Seq a)
    | -- | Traversal exceeded the breadth limit and should not
      -- continue. The last state and the current queue are provided
      -- for analysis.
      Abort (TransitionResult a) (Seq a)
    deriving stock (Eq, Show)

data TraversalResult a
    = -- | remaining queue length and stuck or stopped (unproven)
      -- results (always at most maxCounterExamples many).
      GotStuck Int [a]
    | -- | queue length (exceeding the limit) and result(s) of the
      -- last step that led to stopping.
      Aborted Int [a]
    | -- | queue empty, results returned
      Ended [a]
    deriving stock (Eq, Show)

instance Pretty a => Pretty (TraversalResult a) where
    pretty = \case
        GotStuck n as ->
            Pretty.hang 4 . Pretty.vsep $
                ("Got stuck with queue of " <> Pretty.pretty n) :
                map Pretty.pretty as
        Aborted n as ->
            Pretty.hang 4 . Pretty.vsep $
                ("Aborted with queue of " <> Pretty.pretty n) :
                map Pretty.pretty as
        Ended as ->
            Pretty.hang 4 . Pretty.vsep $
                "Ended" : map Pretty.pretty as

instance Functor TraversalResult where
    fmap f = \case
        GotStuck n rs -> GotStuck n (map f rs)
        Aborted n rs -> Aborted n (map f rs)
        Ended rs -> Ended (map f rs)

----------------------------------------
-- constructing transition functions (for caller)

{- | Construct a transit function for the traversal from its primitive
 steps @prim@ and an interpretation of resulting next states to
 yield a @TransitionResult@.
-}
simpleTransition ::
    forall config m instr rule.
    Monad m =>
    -- | primitive transition applying a rule
    (instr -> config -> TransitionT rule m config) ->
    -- | interprets the config (claim or program state) and rules
    (config -> [config] -> TransitionResult config) ->
    TState instr config ->
    m (TransitionResult (TState instr config))
simpleTransition apply mapToResult = tt
  where
    tt :: TState instr config -> m (TransitionResult (TState instr config))
    tt TState{nextSteps, currentState = config} =
        case nextSteps of
            [] ->
                pure $ fmap (TState []) $ mapToResult config []
            [] : iss ->
                tt $ TState iss config
            is : iss ->
                (fmap (TState iss) . mapToResult config . map fst)
                    <$> runTransitionT (foldM (flip apply) config is)

{- | Construct a transit function for the traversal from its primitive
 steps @prim@ and an interpretation of resulting next states _and
 applied rules_ to yield a @TransitionResult@.

 The rule can be considered to implement e.g. stopping when a
 particular rule (such as unrolling a loop) has been applied.
-}

{- | Construct a transit function for the traversal from its primitive
 steps @prim@ and an interpretation of resulting next states _and
 applied rules_ to yield a @TransitionResult@.

 The rule can be considered to implement e.g. stopping when a
 particular rule (such as unrolling a loop) has been applied.
-}
transitionWithRule ::
    forall config m instr rule.
    Monad m =>
    -- | primitive transition applying a rule
    (instr -> config -> TransitionT rule m config) ->
    -- | interprets the config (claim or program state) and rules
    (config -> [(config, Seq rule)] -> TransitionResult config) ->
    TState instr config ->
    m (TransitionResult (TState instr config))
transitionWithRule apply mapToResult = tt
  where
    tt :: TState instr config -> m (TransitionResult (TState instr config))
    tt TState{nextSteps, currentState = config} =
        case nextSteps of
            [] ->
                pure $ fmap (TState []) $ mapToResult config []
            [] : iss ->
                tt $ TState iss config
            is : iss ->
                (fmap (TState iss) . mapToResult config)
                    <$> runTransitionT (foldM (flip apply) config is)
