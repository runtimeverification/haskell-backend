module GraphTraversal (
    module GraphTraversal,
) where

import Control.Monad.Logic
import Control.Monad.Trans.State
import Data.Limit
import Data.List.NonEmpty qualified as NE
import Data.Sequence (Seq (..))
import Data.Sequence qualified as Seq
import GHC.Generics qualified as GHC
import GHC.Natural
import Kore.Rewrite.Strategy (
    GraphSearchOrder (..),
    LimitExceeded (..),
    TransitionT (..),
    runTransitionT,
    unfoldSearchOrder,
 )
import Prelude.Kore

data TransitionResult a
    = -- | straight-line execution
      StraightLine a
    | -- | branch point
      Branch (NonEmpty a)
    | -- | no next state but not final (e.g., not goal state, or side
      -- conditions do not hold)
      Stuck a
    | -- | final state (e.g., goal state reached, side conditions hold)
      Final a
    | -- Future work:

      -- | config matches a terminal pattern (or: is RHS of a
      -- "terminal" rule) Needs to return that RHS
      Terminal a
    | -- | config matches a cut pattern ( aka: is LHS of a "cut" rule)
      -- The respective RHS (or RHSs) are returned (if any)
      Cut a [a]
    deriving stock (Eq, Show, GHC.Generic)

instance Functor TransitionResult where
    fmap f = \case
        StraightLine a -> StraightLine $ f a
        Branch as -> Branch $ NE.map f as
        Stuck a -> Stuck $ f a
        Final a -> Final $ f a
        Terminal a -> Terminal $ f a
        Cut a as -> Cut (f a) (map f as)

-- Graph traversal would always stop at Terminal/Cut, and _may_ stop
-- at Branch, depending on configuration.

isStuck, isFinal, isTerminal, isCut, isBranch :: TransitionResult a -> Bool
isStuck (Stuck _) = True
isStuck _ = False
isFinal (Final _) = True
isFinal _ = False
isBranch (Branch _) = True
isBranch _ = False
isTerminal (Terminal _) = True
isTerminal _ = False
isCut (Cut _ _) = True
isCut _ = False

extractNext :: TransitionResult a -> [a]
extractNext = \case
    StraightLine a -> [a]
    Branch as -> NE.toList as
    Stuck _ -> []
    Final _ -> []
    Terminal _ -> []
    Cut _ as -> as

extractState :: TransitionResult a -> Maybe a
extractState = \case
    StraightLine _ -> Nothing
    Branch _ -> Nothing
    Stuck a -> Just a
    Final a -> Just a
    Terminal a -> Just a
    Cut a _ -> Just a

----------------------------------------
transitionLeaves ::
    forall m a.
    (Monad m) =>
    -- | Stop critera, in terms of 'TransitionResult's. The algorithm
    -- will _always_ stop on 'Stuck' and 'Final', so [isTerminal,
    -- isCut, isBranch] could be used here. Could simplify this to
    -- FinalNodeType
    [TransitionResult a -> Bool] ->
    -- queue updating parameters,
    -- we construct enqueue :: [a] -> Seq a -> m (Either LimitExceeded (Seq a)) from it
    -- m is probably only there for logging purposes

    -- | BreadthFirst, DepthFirst
    GraphSearchOrder ->
    -- | breadth limit, essentially a natural number
    Limit Natural ->
    -- | transition function
    (a -> m (TransitionResult a)) ->
    -- again, m is probably only for logging

    -- | max-counterexamples, included in the internal logic
    Natural ->
    -- | initial node
    a ->
    m (TraversalResult a)
transitionLeaves
    stopCriteria
    direction
    breadthLimit
    transit
    maxCounterExamples
    start =
        evalStateT (worker $ Seq.singleton start) []
      where
        enqueue' = unfoldSearchOrder direction

        enqueue :: [a] -> Seq a -> m (Either (LimitExceeded a) (Seq a))
        enqueue as q = do
            newQ <- enqueue' as q
            pure $
                if exceedsLimit newQ
                    then Left (LimitExceeded newQ)
                    else Right newQ

        exceedsLimit :: Seq a -> Bool
        exceedsLimit = not . withinLimit breadthLimit . fromIntegral . Seq.length

        shouldStop :: TransitionResult a -> Bool
        shouldStop result = any ($ result) stopCriteria

        maxStuck = fromIntegral maxCounterExamples

        worker :: Seq a -> StateT [TransitionResult a] m (TraversalResult a)
        worker Seq.Empty = Ended <$> get
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
                            if length stuck >= maxStuck
                                then
                                    pure $
                                        GotStuck (Seq.length nextQ) stuck
                                else worker nextQ
                Abort results queue -> do
                    pure $ Aborted (Seq.length queue) results -- FIXME ??? results ???
        step ::
            a ->
            Seq a ->
            m (StepResult a)
        step a q = do
            next <- transit a
            if (isStuck next || isFinal next || shouldStop next)
                then pure (Output next q)
                else
                    either (\(LimitExceeded longQ) -> Abort [next] longQ) Continue
                        <$> enqueue (extractNext next) q

data StepResult a
    = Continue (Seq a)
    | Output (TransitionResult a) (Seq a)
    | Abort [TransitionResult a] (Seq a)

data TraversalResult a
    = -- | remaining queue length and all stuck states
      GotStuck Int [TransitionResult a]
    | -- | remaining queue length (limit exceeded) and results so far
      Aborted Int [TransitionResult a]
    | -- queue ran empty, results returned
      Ended [TransitionResult a]

----------------------------------------
-- constructing transition functions (for caller)

simpleTransition ::
    forall instr config m rule.
    Monad m =>
    -- | primitive strategy rule
    (instr -> config -> TransitionT rule m config) ->
    -- | converter to interpret the config (claim state or program state)
    (config -> [config] -> TransitionResult config) ->
    -- final transition function
    ([instr], config) ->
    m (TransitionResult ([instr], config))
simpleTransition applyPrim mapToResult = uncurry tt
  where
    tt :: [instr] -> config -> m (TransitionResult ([instr], config))
    tt [] config =
        pure . fmap ([],) . (mapToResult config) $ [config]
    tt (i : is) config =
        (fmap (is,) . mapToResult config . map fst)
            <$> runTransitionT (applyPrim i config)
