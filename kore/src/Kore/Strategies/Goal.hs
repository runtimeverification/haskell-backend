{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.Goal where

import Control.Applicative
    ( Alternative (..)
    )
import qualified Data.Foldable as Foldable
import Data.Maybe
    ( mapMaybe
    )
import qualified Generics.SOP as SOP
import GHC.Generics as GHC

import Kore.Debug
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Step.Rule
    ( OnePathRule (..)
    , RewriteRule (..)
    )
import Kore.Step.Simplification.Data
    ( MonadSimplify
    , SimplifierVariable
    )
import Kore.Step.Strategy
    ( Strategy
    )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Strategies.OnePath.Actions as OnePath
import Kore.Strategies.ProofState
import Kore.Unparser
    ( Unparse
    )

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

{- | Does the 'Strategy.ExecutionGraph' indicate a successful proof?
 -}
proven :: Strategy.ExecutionGraph (ProofState goal) rule -> Bool
proven = Foldable.null . unprovenNodes

{- | The primitive transitions of the all-path reachability proof strategy.
 -}
data Prim rule
    = CheckProven
    -- ^ End execution on this branch if the state is 'Proven'.
    | CheckGoalRemainder
    -- ^ End execution on this branch if the state is 'GoalRemainder'.
    | ResetGoalRewritten
    -- ^ Mark all goals rewritten previously as new goals.
    | Simplify
    | RemoveDestination
    | TriviallyValid
    | DerivePar [rule]
    | DeriveSeq [rule]
    deriving (Show)

class Goal goal where
    data Rule goal

    -- | Remove the destination of the goal.
    removeDestination
        :: MonadSimplify m
        => goal
        -> Strategy.TransitionT (Rule goal) m goal

    simplify
        :: MonadSimplify m
        => goal
        -> Strategy.TransitionT (Rule goal) m goal

    isTriviallyValid :: goal -> Bool

    isTrusted :: goal -> Bool

    -- | Apply 'Rule's to the goal in parallel.
    derivePar
        :: MonadSimplify m
        => [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)

    -- | Apply 'Rule's to the goal in sequence.
    deriveSeq
        :: MonadSimplify m
        => [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)

transitionRule
    :: (MonadSimplify m, Goal goal)
    => Prim (Rule goal)
    -> ProofState goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal)
transitionRule = transitionRuleWorker
  where
    transitionRuleWorker CheckProven Proven = empty
    transitionRuleWorker CheckGoalRemainder (GoalRemainder _) = empty

    transitionRuleWorker ResetGoalRewritten (GoalRewritten goal) =
        return (Goal goal)

    transitionRuleWorker Simplify (Goal g) =
        Goal <$> simplify g
    transitionRuleWorker Simplify (GoalRemainder g) =
        GoalRemainder <$> simplify g

    transitionRuleWorker RemoveDestination (Goal g) =
        Goal <$> removeDestination g
    transitionRuleWorker RemoveDestination (GoalRemainder g) =
        GoalRemainder <$> removeDestination g

    transitionRuleWorker TriviallyValid (Goal g)
      | isTriviallyValid g = return Proven
    transitionRuleWorker TriviallyValid (GoalRemainder g)
      | isTriviallyValid g = return Proven
    transitionRuleWorker TriviallyValid (GoalRewritten g)
      | isTriviallyValid g = return Proven

    transitionRuleWorker (DerivePar rules) (Goal g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        derivePar rules g
    transitionRuleWorker (DerivePar rules) (GoalRemainder g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        derivePar rules g

    transitionRuleWorker (DeriveSeq rules) (Goal g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        deriveSeq rules g
    transitionRuleWorker (DeriveSeq rules) (GoalRemainder g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        deriveSeq rules g

    transitionRuleWorker _ state = return state

allPathStrategy
    :: [rule]
    -- ^ Claims
    -> [rule]
    -- ^ Axioms
    -> [Strategy (Prim rule)]
allPathStrategy claims axioms =
    firstStep : repeat nextStep
  where
    firstStep =
        (Strategy.sequence . map Strategy.apply)
            [ CheckProven
            , CheckGoalRemainder
            , RemoveDestination
            , TriviallyValid
            , DerivePar axioms
            , RemoveDestination
            , Simplify
            , TriviallyValid
            , ResetGoalRewritten
            , TriviallyValid
            ]
    nextStep =
        (Strategy.sequence . map Strategy.apply)
            [ CheckProven
            , CheckGoalRemainder
            , RemoveDestination
            , TriviallyValid
            , DeriveSeq claims
            , RemoveDestination
            , Simplify
            , TriviallyValid
            , DerivePar axioms
            , RemoveDestination
            , Simplify
            , TriviallyValid
            , ResetGoalRewritten
            , TriviallyValid
            ]

onePathFirstStep :: [rule] -> Strategy (Prim rule)
onePathFirstStep axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq axioms
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , ResetGoalRewritten
        , Simplify
        , TriviallyValid
        ]

onePathFollowupStep :: [rule] -> [rule] -> Strategy (Prim rule)
onePathFollowupStep claims axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq claims
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq axioms
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , ResetGoalRewritten
        , Simplify
        , TriviallyValid
        ]

instance (SimplifierVariable variable) => Goal (OnePathRule variable) where

    newtype Rule (OnePathRule variable) =
        Rule { unRule :: RewriteRule variable }
        deriving (GHC.Generic, Show, Unparse)

    isTrusted = OnePath.isTrusted

    removeDestination = OnePath.removeDestination

    simplify = OnePath.simplify

    isTriviallyValid = OnePath.isTriviallyValid

    derivePar = OnePath.derivePar

    deriveSeq = OnePath.deriveSeq

instance SOP.Generic (Rule (OnePathRule variable))

instance SOP.HasDatatypeInfo (Rule (OnePathRule variable))

instance Debug variable => Debug (Rule (OnePathRule variable))
