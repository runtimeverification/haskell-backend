{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Goal where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Data.Foldable as Foldable
import           Data.Maybe
                 ( mapMaybe )
import qualified Generics.SOP as SOP
import           GHC.Generics as GHC

import           Kore.Debug
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.TermLike
import           Kore.ProofState
import           Kore.Step.Rule
                 ( OnePathRule (..), RewriteRule (..) )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify )
import           Kore.Step.Strategy
                 ( Strategy )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Strategies.OnePath.Actions as OnePath
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

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
    | CheckGoalRem
    -- ^ End execution on this branch if the state is 'GoalRem'.
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
    transitionRuleWorker CheckGoalRem (GoalRem _) = empty

    transitionRuleWorker Simplify (Goal g) =
        Goal <$> simplify g
    transitionRuleWorker Simplify (GoalRem g) =
        GoalRem <$> simplify g

    transitionRuleWorker RemoveDestination (Goal g) =
        GoalRem <$> removeDestination g

    transitionRuleWorker TriviallyValid (Goal g)
      | isTriviallyValid g = return Proven
    transitionRuleWorker TriviallyValid (GoalRem g)
      | isTriviallyValid g = return Proven

    transitionRuleWorker (DerivePar rules) (GoalRem g) =
        derivePar rules g

    transitionRuleWorker (DeriveSeq rules) (GoalRem g) =
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
            , CheckGoalRem
            , RemoveDestination
            , TriviallyValid
            , DerivePar axioms
            , TriviallyValid
            ]
    nextStep =
        (Strategy.sequence . map Strategy.apply)
            [ CheckProven
            , CheckGoalRem
            , RemoveDestination
            , TriviallyValid
            , DeriveSeq claims
            , DerivePar axioms
            , TriviallyValid
            ]

onePathFirstStep :: [rule] -> Strategy (Prim rule)
onePathFirstStep axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRem
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq axioms
        , Simplify
        , TriviallyValid
        ]

onePathFollowupStep :: [rule] -> [rule] -> Strategy (Prim rule)
onePathFollowupStep claims axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRem
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq claims
        , DeriveSeq axioms
        , Simplify
        , TriviallyValid
        ]

instance
    ( SortedVariable variable
    , Debug variable
    , Unparse variable
    , Show variable
    , FreshVariable variable
    ) => Goal (OnePathRule variable) where

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
