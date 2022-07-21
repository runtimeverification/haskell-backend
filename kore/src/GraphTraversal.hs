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
import Kore.Reachability.Prim (Prim)
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
    | -- | branch point (1st arg), branching into 2nd arg elements
      Branch a (NonEmpty a)
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
        Branch a as -> Branch (f a) $ NE.map f as
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
isBranch (Branch _ _) = True
isBranch _ = False
isTerminal (Terminal _) = True
isTerminal _ = False
isCut (Cut _ _) = True
isCut _ = False

extractNext :: TransitionResult a -> [a]
extractNext = \case
    StraightLine a -> [a]
    Branch _ as -> NE.toList as
    Stuck _ -> []
    Final _ -> []
    Terminal _ -> []
    Cut _ as -> as

extractState :: TransitionResult a -> Maybe a
extractState = \case
    StraightLine _ -> Nothing
    Branch a _ -> Just a
    Stuck a -> Just a
    Final a -> Just a
    Terminal a -> Just a
    Cut a _ -> Just a

type Step = [Prim]

----------------------------------------
transitionLeaves ::
    forall m c.
    (Monad m) =>
    -- | Stop critera, in terms of 'TransitionResult's. The algorithm
    -- will _always_ stop on 'Stuck' and 'Final', so [isTerminal,
    -- isCut, isBranch] could be used here. Could simplify this to
    -- FinalNodeType
    [TransitionResult ([Step], c) -> Bool] ->
    -- queue updating parameters,
    -- we construct enqueue :: [a] -> Seq a -> m (Either LimitExceeded (Seq a)) from it
    -- m is probably only there for logging purposes

    -- | BreadthFirst, DepthFirst
    GraphSearchOrder ->
    -- | breadth limit, essentially a natural number
    Limit Natural ->
    -- | transition function
    (([Step], c) -> m (TransitionResult ([Step], c))) ->
    -- again, m is probably only for logging

    -- | max-counterexamples, included in the internal logic
    Natural ->
    -- | initial node
    ([Step], c) ->
    m (TraversalResult c)
transitionLeaves
    stopCriteria
    direction
    breadthLimit
    transit
    maxCounterExamples
    start =
        evalStateT (worker (Seq.singleton start) >>= checkLeftUnproven) []
      where
        enqueue' = unfoldSearchOrder direction

        enqueue :: [([Step], c)] -> Seq ([Step], c) -> m (Either (LimitExceeded ([Step], c)) (Seq ([Step], c)))
        enqueue as q = do
            newQ <- enqueue' as q
            pure $
                if exceedsLimit newQ
                    then Left (LimitExceeded newQ)
                    else Right newQ

        exceedsLimit :: Seq ([Step], c) -> Bool
        exceedsLimit = not . withinLimit breadthLimit . fromIntegral . Seq.length

        shouldStop :: TransitionResult ([Step], c) -> Bool
        shouldStop result = any ($ result) stopCriteria

        maxStuck = fromIntegral maxCounterExamples

        worker :: Seq ([Step], c) -> StateT [TransitionResult ([Step], c)] m (TraversalResult ([Step], c))
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
            ([Step], c) ->
            Seq ([Step], c) ->
            m (StepResult ([Step], c))
        step a q = do
            next <- transit a
            if (isStuck next || isFinal next || shouldStop next)
                then pure (Output next q)
                else
                    either (\(LimitExceeded longQ) -> Abort [next] longQ) Continue
                        <$> enqueue (extractNext next) q

        checkLeftUnproven ::
            TraversalResult ([Step], c) ->
            StateT [TransitionResult ([Step], c)] m (TraversalResult c)
        checkLeftUnproven result = do
            stuck <- gets (map (fmap snd) . filter isStuck)
            pure $
                if null stuck
                    then fmap snd result
                    else GotStuck 0 stuck

data StepResult a
    = Continue (Seq a)
    | Output (TransitionResult a) (Seq a)
    | Abort [TransitionResult a] (Seq a)
    deriving stock (Eq, Show, GHC.Generic)

data TraversalResult a
    = -- | remaining queue length and all stuck states
      GotStuck Int [TransitionResult a]
    | -- | remaining queue length (limit exceeded) and results so far
      Aborted Int [TransitionResult a]
    | -- queue ran empty, results returned
      Ended [TransitionResult a]
    deriving stock (Eq, Show, GHC.Generic)

instance Functor TraversalResult where
    fmap f = \case
        GotStuck n rs -> GotStuck n (ffmap f rs)
        Aborted n rs -> GotStuck n (ffmap f rs)
        Ended rs -> Ended (ffmap f rs)
      where
        ffmap = map . fmap

----------------------------------------
-- constructing transition functions (for caller)

simpleTransition ::
    forall config m rule.
    Monad m =>
    -- | primitive strategy rule
    (Prim -> config -> TransitionT rule m config) ->
    -- | converter to interpret the config (claim state or program state)
    (config -> [config] -> TransitionResult config) ->
    -- final transition function
    ([Step], config) ->
    m (TransitionResult ([Step], config))
simpleTransition applyPrim mapToResult = uncurry tt
  where
    tt :: [Step] -> config -> m (TransitionResult ([Step], config))
    tt [] config =
        pure $ Final ([], config)
    tt ([] : iss) config =
        tt iss config
    tt (is : iss) config =
        (fmap (iss,) . mapToResult config . map fst)
            <$> runTransitionT (applyGroup is config)

    applyGroup :: Step -> config -> TransitionT rule m config
    applyGroup is c = foldM (flip applyPrim) c is
