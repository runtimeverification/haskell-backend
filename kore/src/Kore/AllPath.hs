{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.AllPath where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Monad.Trans as Monad.Trans
import           Data.Maybe
                 ( mapMaybe )

import qualified Kore.Step.Representation.MultiOr as MultiOr
import qualified Kore.Step.Strategy as Strategy

{- | The state of the all-path reachability proof strategy for @goal@.
 -}
data ProofState goal
    = Goal goal
    -- ^ The indicated goal is being proven.
    | GoalRem goal
    -- ^ The indicated goal remains after rewriting.
    | Proven
    -- ^ The parent goal was proven.
    deriving (Eq, Show)

{- | Extract the unproven goals of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ProofState goal -> Maybe goal
extractUnproven (Goal t)    = Just t
extractUnproven (GoalRem t) = Just t
extractUnproven Proven      = Nothing

{- | The final nodes of an execution graph which were not proven.

See also: 'Strategy.pickFinal', 'extractUnproven'

 -}
unprovenNodes
    :: Strategy.ExecutionGraph (ProofState goal) rule
    -> MultiOr.MultiOr goal
unprovenNodes executionGraph =
    MultiOr.MultiOr
    $ mapMaybe extractUnproven
    $ Strategy.pickFinal executionGraph

data Prim rule
    = CheckProven
    | CheckGoalRem
    | RemoveDestination
    | TriviallyValid

transitionRule
    :: Monad m
    => (goal -> Strategy.TransitionT rule m goal)
    -- ^ Remove destination from goal
    -> (goal -> m Bool)
    -- ^ Check goal
    -> Prim rule
    -> ProofState goal
    -> Strategy.TransitionT rule m (ProofState goal)
transitionRule removeDestination checkGoal = transitionRuleWorker
  where
    transitionRuleWorker CheckProven state =
        case state of
            Proven -> empty
            _      -> return state

    transitionRuleWorker CheckGoalRem state =
        case state of
            GoalRem _ -> empty
            _         -> return state

    transitionRuleWorker RemoveDestination state =
        case state of
            Proven    -> return Proven
            GoalRem _ -> empty
            Goal    g -> GoalRem <$> removeDestination g

    transitionRuleWorker TriviallyValid state =
        case state of
            GoalRem g -> do
                valid <- Monad.Trans.lift (checkGoal g)
                if valid then return Proven else return state
            _         -> return state
