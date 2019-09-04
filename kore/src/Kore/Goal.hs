{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Goal where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Monad.Trans as Monad.Trans
import           Data.Coerce
                 ( Coercible, coerce )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import           Data.Hashable
import           Data.Maybe
                 ( mapMaybe )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import           GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Trusted as Trusted
import           Kore.Debug
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
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
                 ( MonadSimplify, SimplifierVariable )
import           Kore.Step.Simplification.Pattern
                 ( simplifyAndRemoveTopExists )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import qualified Kore.Step.Step as Step
import           Kore.Step.Strategy
                 ( Strategy )
import qualified Kore.Step.Strategy as Strategy
import           Kore.TopBottom
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse, unparse )
import           Kore.Variables.UnifiedVariable

{- | The state of the all-path reachability proof strategy for @goal@.
 -}
data ProofState goal
    = Goal goal
    -- ^ The indicated goal is being proven.
    | GoalRem goal
    -- ^ The indicated goal remains after rewriting.
    | Proven
    -- ^ The parent goal was proven.
    deriving (Eq, Show, Ord, Functor, Generic)

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

{- | The predicate to remove the destination from the present configuration.
 -}
removalPredicate
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        )
    => Pattern variable
    -- ^ Destination
    -> Pattern variable
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
        extraVariables = Set.toList
            $ Set.difference destinationVariables configVariables
        extraElementVariables = [v | ElemVar v <- extraVariables]
        extraNonElemVariables = filter (not . isElemVar) extraVariables
        quantifyPredicate = Predicate.makeMultipleExists extraElementVariables
    in
        if not (null extraNonElemVariables)
        then error
            ("Cannot quantify non-element variables: "
                ++ show (unparse <$> extraNonElemVariables))
        else Predicate.makeNotPredicate
            $ quantifyPredicate
            $ Predicate.makeCeilPredicate
            $ mkAnd
                (Pattern.toTermLike destination)
                (Pattern.toTermLike config)

instance
    (SimplifierVariable variable , Debug variable)
    => Goal (OnePathRule variable)
  where

    newtype Rule (OnePathRule variable) =
        Rule { unRule :: RewriteRule variable }
        deriving (GHC.Generic, Show, Unparse)

    isTrusted =
        Trusted.isTrusted
        . Attribute.trusted
        . attributes
        . coerce

    removeDestination goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
            removal = removalPredicate destination configuration
            result = Conditional.andPredicate configuration removal
        pure $ makeRuleFromPatterns result destination

    simplify goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
        configs <-
            Monad.Trans.lift
            $ simplifyAndRemoveTopExists configuration
        filteredConfigs <- SMT.Evaluator.filterMultiOr configs
        if null filteredConfigs
           then pure $ makeRuleFromPatterns Pattern.bottom destination
           else do
               let simplifiedRules =
                       fmap (flip makeRuleFromPatterns destination) filteredConfigs
               Foldable.asum (pure <$> simplifiedRules)


    isTriviallyValid =
        isBottom . left . coerce

    derivePar rules goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
            rewrites = unRule <$> rules
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
                            removeDestSimplifyRemainder
                let onePathResults =
                        Result.mapConfigs
                            (flip makeRuleFromPatterns $ destination)
                            (flip makeRuleFromPatterns $ destination)
                            (Result.mergeResults results)
                results' <-
                    traverseConfigs (mapRules onePathResults)
                Result.transitionResults results'

    deriveSeq rules goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
            rewrites = unRule <$> rules
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
                            removeDestSimplifyRemainder
                let onePathResults =
                        Result.mapConfigs
                            (flip makeRuleFromPatterns $ destination)
                            (flip makeRuleFromPatterns $ destination)
                            (Result.mergeResults results)
                results' <-
                    traverseConfigs (mapRules onePathResults)
                Result.transitionResults results'

instance SOP.Generic (Rule (OnePathRule variable))

instance SOP.HasDatatypeInfo (Rule (OnePathRule variable))

instance Debug variable => Debug (Rule (OnePathRule variable))

removeDestSimplifyRemainder
    :: forall variable m
    .  MonadSimplify m
    => SimplifierVariable variable
    => Debug variable
    => OnePathRule variable
    -> Strategy.TransitionT (Rule (OnePathRule variable)) m (ProofState (OnePathRule variable))
removeDestSimplifyRemainder remainder = do
    result <- removeDestination remainder >>= simplify
    if isTriviallyValid result
       then pure Proven
       else pure . GoalRem $ result

getConfiguration
    :: forall rule variable
    .  Ord variable
    => Coercible rule (RulePattern variable)
    => rule
    -> Pattern variable
getConfiguration (coerce -> RulePattern { left, requires }) =
    Pattern.withCondition left (Conditional.fromPredicate requires)

getDestination
    :: forall rule variable
    .  Ord variable
    => Coercible rule (RulePattern variable)
    => rule
    -> Pattern variable
getDestination (coerce -> RulePattern { right, ensures }) =
    Pattern.withCondition right (Conditional.fromPredicate ensures)

makeRuleFromPatterns
    :: forall rule variable
    .  Ord variable
    => SortedVariable variable
    => Unparse variable
    => Show variable
    => Coercible (RulePattern variable) rule
    => Pattern variable
    -> Pattern variable
    -> rule
makeRuleFromPatterns configuration destination =
    let (left, Conditional.toPredicate -> requires) = Pattern.splitTerm configuration
        (right, Conditional.toPredicate -> ensures) = Pattern.splitTerm destination
    in coerce RulePattern { left, right, requires, ensures, attributes = Default.def }
