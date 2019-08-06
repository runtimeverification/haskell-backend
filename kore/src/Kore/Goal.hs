{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Goal where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Monad.Trans as Monad.Trans
import           Data.Coerce
                 ( coerce )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import           Data.Hashable
import           Data.Maybe
                 ( mapMaybe )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Trusted as Trusted
import           Kore.Internal.Conditional
                 ( Conditional (..) )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Step.Result as Result
import           Kore.Step.Rule
                 ( OnePathRule (..), RewriteRule (..), RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify )
import           Kore.Step.Simplification.Pattern
                 ( simplifyAndRemoveTopExists )
import qualified Kore.Step.Step as Step
import           Kore.Step.Strategy
                 ( Strategy )
import qualified Kore.Step.Strategy as Strategy
import           Kore.TopBottom
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse, unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )
import qualified Kore.Variables.Target as Target

{- | The state of the all-path reachability proof strategy for @goal@.
 -}
data ProofState goal
    = Goal goal
    -- ^ The indicated goal is being proven.
    | GoalRem goal
    -- ^ The indicated goal remains after rewriting.
    | Proven
    -- ^ The parent goal was proven.
    deriving (Eq, Show, Ord, Functor, GHC.Generic)

instance Hashable goal => Hashable (ProofState goal)

{- | Extract the unproven goals of a 'ProofState'.

Returns 'Nothing' if there is no remaining unproven goal.

 -}
extractUnproven :: ProofState goal -> Maybe goal
extractUnproven (Goal t)    = Just t
extractUnproven (GoalRem t) = Just t
extractUnproven Proven      = Nothing

extractGoalRem :: ProofState goal -> Maybe goal
extractGoalRem (GoalRem t) = Just t
extractGoalRem _           = Nothing

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

data ProofStateTransformer goal a =
    ProofStateTransformer
        { goalTransformer :: goal -> a
        , goalRemTransformer :: goal -> a
        , provenValue :: a
        }

{- | Catamorphism for 'ProofState'
-}
proofState
    :: ProofStateTransformer goal a
    -> ProofState goal
    -> a
proofState
    ProofStateTransformer
        {goalTransformer, goalRemTransformer, provenValue}
  =
    \case
        Goal goal -> goalTransformer goal
        GoalRem goal -> goalRemTransformer goal
        Proven -> provenValue

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

class ( SortedVariable variable
      , Ord variable
      , Unparse variable
      , Show variable
      , FreshVariable variable
      ) => Goal goal variable where
    data Rule goal :: * -> *

    -- | Remove the destination of the (goal variable).
    removeDestination
        :: MonadSimplify m
        => (goal variable)
        -> Strategy.TransitionT ((Rule goal) variable) m (goal variable)

    simplify
        :: MonadSimplify m
        => (goal variable)
        -> Strategy.TransitionT ((Rule goal) variable) m (goal variable)

    isTriviallyValid :: (goal variable) -> Bool

    isTrusted :: (goal variable) -> Bool

    -- | Apply 'Rule's in to the (goal variable) in parallel.
    derivePar
        :: MonadSimplify m
        => [(Rule goal) variable]
        -> (goal variable)
        -> Strategy.TransitionT ((Rule goal) variable) m (ProofState (goal variable))

    -- | Apply 'Rule's in to the (goal variable) in sequence.
    deriveSeq
        :: MonadSimplify m
        => [(Rule goal) variable]
        -> (goal variable)
        -> Strategy.TransitionT ((Rule goal) variable) m (ProofState (goal variable))

    to :: (goal variable) -> RulePattern variable

    from :: RulePattern variable -> (goal variable)

    ruleTo :: (Rule goal) variable -> RulePattern variable

    ruleFrom :: RulePattern variable -> (Rule goal) variable

transitionRule
    :: (MonadSimplify m, Goal goal variable)
    => Prim ((Rule goal) variable)
    -> ProofState (goal variable)
    -> Strategy.TransitionT ((Rule goal) variable) m (ProofState (goal variable))
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

    transitionRuleWorker TriviallyValid (GoalRem g)
      | isTriviallyValid g = return Proven

    transitionRuleWorker (DerivePar rules) (GoalRem g) =
        derivePar rules g

    transitionRuleWorker (DeriveSeq rules) (GoalRem g) =
        deriveSeq rules g

    transitionRuleWorker _ state = return state

strategy
    :: [rule]
    -- ^ Claims
    -> [rule]
    -- ^ Axioms
    -> [Strategy (Prim rule)]
strategy claims axioms =
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
            , DerivePar claims
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
        , DerivePar axioms
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
        , DerivePar claims
        , DerivePar axioms
        , Simplify
        , TriviallyValid
        ]

{- | The predicate to remove the destination from the present configuration.
 -}
removalPredicate
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => Pattern.Pattern variable
    -- ^ Destination
    -> Pattern.Pattern variable
    -- ^ Current configuration
    -> Predicate variable
removalPredicate destination config =
    let
        -- The variables of the destination that are missing from the
        -- configuration. These are the variables which should be existentially
        -- quantified in the removal predicate.
        configVariables =
            FreeVariables.getFreeVariables $ Pattern.freeVariables config
        destinationVariables =
            FreeVariables.getFreeVariables $ Pattern.freeVariables destination
        extraVariables = Set.difference destinationVariables configVariables
        quantifyPredicate = Predicate.makeMultipleExists extraVariables
    in
        Predicate.makeNotPredicate
        $ quantifyPredicate
        $ Predicate.makeCeilPredicate
        $ mkAnd
            (Pattern.toTermLike destination)
            (Pattern.toTermLike config)

instance Goal OnePathRule Variable where

    newtype (Rule OnePathRule) Variable =
        Rule { unRule :: RewriteRule Variable }

    isTrusted =
        Trusted.isTrusted
        . Attribute.trusted
        . attributes
        . coerce

    removeDestination goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
            removal =
                removalPredicate destination configuration
            result =
                Conditional.andPredicate
                    configuration
                    removal
        pure $ makeGoal result destination

    simplify goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
        orResult <-
            Monad.Trans.lift
            $ simplifyAndRemoveTopExists configuration
        let simplifiedResult =
                OrPattern.toPattern
                . MultiOr.filterOr
                $ orResult
        pure $ makeGoal simplifiedResult destination

    isTriviallyValid goal =
        isBottom . left . coerce $ goal

    derivePar rules goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
            rewrites = fmap unRule rules
        eitherResults <-
            Monad.Trans.lift
            . Monad.Unify.runUnifierT
            $ Step.applyRewriteRulesParallel
                (Step.UnificationProcedure Unification.unificationProcedure)
                rewrites
                configuration
        case eitherResults of
            Left err ->
                (error . show . Pretty.vsep)
                [ "Not implemented error:"
                , Pretty.indent 4 (Pretty.pretty err)
                , "while applying a \\rewrite axiom to the pattern:"
                , Pretty.indent 4 (unparse configuration)
                ,   "We decided to end the execution because we don't \
                    \understand this case well enough at the moment."
                ]
            Right results -> do
                let mapRules =
                        Result.mapRules
                        $ Rule
                        . RewriteRule
                        . Step.unwrapRule
                        . Step.withoutUnification
                    traverseConfigs =
                        Result.traverseConfigs
                            (pure . Goal)
                            (\x -> GoalRem <$> removeDestination x)
                let onePathResults =
                        Result.mapConfigs
                            (flip makeGoal $ destination)
                            (flip makeGoal $ destination)
                            (Result.mergeResults results)
                results' <-
                    traverseConfigs (mapRules onePathResults)
                Result.transitionResults results'

    deriveSeq rules goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
            rewrites = fmap unRule rules
        eitherResults <-
            Monad.Trans.lift
            . Monad.Unify.runUnifierT
            $ Step.applyRewriteRulesSequence
                (Step.UnificationProcedure Unification.unificationProcedure)
                configuration
                rewrites
        case eitherResults of
            Left err ->
                (error . show . Pretty.vsep)
                [ "Not implemented error:"
                , Pretty.indent 4 (Pretty.pretty err)
                , "while applying a \\rewrite axiom to the pattern:"
                , Pretty.indent 4 (unparse configuration)
                ,   "We decided to end the execution because we don't \
                    \understand this case well enough at the moment."
                ]
            Right results -> do
                let mapRules =
                        Result.mapRules
                        $ Rule
                        . RewriteRule
                        . Step.unwrapRule
                        . Step.withoutUnification
                    traverseConfigs =
                        Result.traverseConfigs
                            (pure . Goal)
                            (\x -> GoalRem <$> removeDestination x)
                let onePathResults =
                        Result.mapConfigs
                            (flip makeGoal $ destination)
                            (flip makeGoal $ destination)
                            (Result.mergeResults results)
                results' <-
                    traverseConfigs (mapRules onePathResults)
                Result.transitionResults results'

getConfiguration
    :: forall goal variable
    .  Goal goal variable
    => goal variable
    -> Pattern variable
getConfiguration goal =
    let RulePattern {left, requires} = to goal in
        Conditional
            { term = left
            , predicate = requires
            , substitution = mempty
            }

getDestination
    :: forall goal variable
    .  Goal goal variable
    => goal variable
    -> Pattern variable
getDestination goal =
    let RulePattern {right, ensures} = to goal in
        Conditional
            { term = right
            , predicate = ensures
            , substitution = mempty
            }

makeGoal
    :: forall goal variable
    .  Goal goal variable
    => Pattern variable
    -> Pattern variable
    -> goal variable
makeGoal configuration destination =
    from RulePattern
        { left = term configuration
        , right = term destination
        , requires = predicate configuration
        , ensures = predicate destination
        , attributes = Default.def
        }
