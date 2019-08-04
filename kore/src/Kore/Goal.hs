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
import qualified Data.Foldable as Foldable
import           Data.Hashable
import           Data.Maybe
                 ( mapMaybe )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Generics

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Trusted as Trusted
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrPattern as OrPattern
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
    deriving (Eq, Show, Ord, Generic)

instance Hashable goal => Hashable (ProofState goal)

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

class Goal goal where
    type Rule goal

    -- | Remove the destination of the goal.
    removeDestination
        :: MonadSimplify m
        => goal
        -> Strategy.TransitionT (Rule goal) m goal

    applySimplify
        :: MonadSimplify m
        => (goal -> ProofState goal)
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)

    isTriviallyValid :: goal -> Bool

    isTrusted :: goal -> Bool

    -- | Apply 'Rule's in to the goal in parallel.
    derivePar
        :: MonadSimplify m
        => [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)

    -- | Apply 'Rule's in to the goal in sequence.
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
        applySimplify Goal g
    transitionRuleWorker Simplify (GoalRem g) =
        applySimplify GoalRem g

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
    (firstStep claims axioms)
    : (repeat $ nextStep claims axioms)

firstStep
    :: [rule] -> [rule] -> Strategy (Prim rule)
firstStep claims axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRem
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DerivePar axioms
        , Simplify
        , TriviallyValid
        ]

nextStep
    :: [rule] -> [rule] -> Strategy (Prim rule)
nextStep claims axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRem
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

instance
    ( SortedVariable variable
    , Ord variable
    , Unparse variable
    , Show variable
    , FreshVariable variable
    ) => Goal (OnePathRule variable) where

    type Rule (OnePathRule variable) = RewriteRule variable

    isTrusted =
        Trusted.isTrusted
        . Attribute.trusted
        . attributes
        . coerce

    removeDestination goal = do
        let destination =
                Pattern.fromTermLike
                . right
                . coerce
                $ goal
            configuration =
                Pattern.fromTermLike
                . left
                . coerce
                $ goal
            removal =
                removalPredicate destination configuration
            result =
                Conditional.andPredicate
                    configuration
                    removal
        orResult <-
            Monad.Trans.lift
            $ simplifyAndRemoveTopExists result
        let simplifiedResult = MultiOr.filterOr orResult
        pure . OnePathRule
            $ RulePattern
                { left = OrPattern.toTermLike simplifiedResult
                , right = right . coerce $ goal
                , requires = requires . coerce $ goal
                , ensures = ensures . coerce $ goal
                , attributes = attributes . coerce $ goal
                }

    applySimplify wrapper goal = do
        orResult <-
            Monad.Trans.lift
            $ simplifyAndRemoveTopExists (Pattern.fromTermLike . left . coerce $ goal)
        let simplifiedResult = MultiOr.filterOr orResult
        pure . wrapper . OnePathRule
            $ RulePattern
                { left = OrPattern.toTermLike simplifiedResult
                , right = right . coerce $ goal
                , requires = requires . coerce $ goal
                , ensures = ensures . coerce $ goal
                , attributes = attributes . coerce $ goal
                }

    isTriviallyValid goal =
        isBottom . left . coerce $ goal

    derivePar rules goal = do
        let destination =
                Pattern.fromTermLike
                . right
                . coerce
                $ goal
            configuration =
                Pattern.fromTermLike
                . left
                . coerce
                $ goal
        if isBottom configuration
            then empty
            else do
                eitherResults <-
                    Monad.Trans.lift
                    . Monad.Unify.runUnifierT
                    $ Step.applyRewriteRulesParallel
                        (Step.UnificationProcedure Unification.unificationProcedure)
                        rules
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
                        let
                            mapRules
                                :: Result.Results (Step.UnifiedRule (Target.Target variable)) (OnePathRule variable)
                                -> Result.Results (RewriteRule variable) (OnePathRule variable)
                            mapRules =
                                Result.mapRules
                                $ RewriteRule
                                . Step.unwrapRule
                                . Step.withoutUnification
                            -- Try one last time to remove the destination from the
                            -- remainder.
                           -- checkRemainder
                           --     :: OnePathRule variable
                           --     -> Strategy.TransitionT
                           --         (RewriteRule variable)
                           --         m
                           --         (ProofState (OnePathRule variable))
                            checkRemainder remainder = do
                                newClaim <- removeDestination remainder
                                let term = left . coerce $ newClaim
                                if isBottom term
                                   then pure Proven
                                   else pure . GoalRem $ newClaim
                           -- traverseConfigs
                           --     :: Result.Results rule (OnePathRule variable)
                           --     -> Strategy.TransitionT
                           --         (RewriteRule variable)
                           --         m
                           --         (Result.Results
                           --             rule
                           --             (ProofState (OnePathRule variable))
                           --         )
                            traverseConfigs =
                                Result.traverseConfigs
                                    (pure . Goal)
                                    checkRemainder
                            -- makeOnePathRule
                            --     :: Pattern.Pattern variable
                            --     -> OnePathRule variable
                            makeOnePathRule patt =
                                OnePathRule RulePattern
                                    { left = Pattern.toTermLike patt
                                    , right = Pattern.toTermLike destination
                                    , requires = requires . coerce $ goal
                                    , ensures = ensures . coerce $ goal
                                    , attributes = attributes . coerce $ goal
                                    }
                        results' <-
                            traverseConfigs
                                (mapRules
                                    (Result.mapConfigs
                                        makeOnePathRule
                                        makeOnePathRule
                                        (Result.mergeResults results)
                                    )
                                )
                            >>= Result.transitionResults
                        pure results'

    deriveSeq rules goal = do
        let destination =
                Pattern.fromTermLike
                . right
                . coerce
                $ goal
            configuration =
                Pattern.fromTermLike
                . left
                . coerce
                $ goal
        if isBottom configuration
            then empty
            else do
                eitherResults <-
                    Monad.Trans.lift
                    . Monad.Unify.runUnifierT
                    $ Step.applyRewriteRulesSequence
                        (Step.UnificationProcedure Unification.unificationProcedure)
                        configuration
                        rules
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
                        let
                            mapRules
                                :: Result.Results (Step.UnifiedRule (Target.Target variable)) (OnePathRule variable)
                                -> Result.Results (RewriteRule variable) (OnePathRule variable)
                            mapRules =
                                Result.mapRules
                                $ RewriteRule
                                . Step.unwrapRule
                                . Step.withoutUnification
                            -- Try one last time to remove the destination from the
                            -- remainder.
                           -- checkRemainder
                           --     :: OnePathRule variable
                           --     -> Strategy.TransitionT
                           --         (RewriteRule variable)
                           --         m
                           --         (ProofState (OnePathRule variable))
                            checkRemainder remainder = do
                                newClaim <- removeDestination remainder
                                pure . GoalRem $ newClaim
                           -- traverseConfigs
                           --     :: Result.Results rule (OnePathRule variable)
                           --     -> Strategy.TransitionT
                           --         (RewriteRule variable)
                           --         m
                           --         (Result.Results
                           --             rule
                           --             (ProofState (OnePathRule variable))
                           --         )
                            traverseConfigs =
                                Result.traverseConfigs
                                    (pure . Goal)
                                    checkRemainder
                            -- makeOnePathRule
                            --     :: Pattern.Pattern variable
                            --     -> OnePathRule variable
                            makeOnePathRule patt =
                                OnePathRule RulePattern
                                    { left = Pattern.toTermLike patt
                                    , right = Pattern.toTermLike destination
                                    , requires = requires . coerce $ goal
                                    , ensures = ensures . coerce $ goal
                                    , attributes = attributes . coerce $ goal
                                    }
                        results' <-
                            traverseConfigs
                                (mapRules
                                    (Result.mapConfigs
                                        makeOnePathRule
                                        makeOnePathRule
                                        (Result.mergeResults results)
                                    )
                                )
                            >>= Result.transitionResults
                        pure results'
