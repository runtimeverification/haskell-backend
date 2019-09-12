{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.Goal
    ( Goal (..)
    , Rule (..)
    , Prim (..)
    , ProofStrategy (..)
    , unprovenNodes
    , transitionRule
    , allPathStrategy
    , proven
    , getConfiguration
    , getDestination
    , makeRuleFromPatterns
    , makeProofStrategy
    , firstStepStrategy
    , nextStepStrategy
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Monad.Trans as Monad.Trans
import           Data.Coerce
                 ( Coercible, coerce )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import           Data.Maybe
                 ( mapMaybe )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import           GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute.FreeVariables
import qualified Kore.Attribute.Trusted as Attribute.Trusted
import           Kore.Debug
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
                 ( mkAnd )
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Predicate.Predicate as Syntax
import qualified Kore.Step.Result as Result
import           Kore.Step.Rule
                 ( AllPathRule (..), OnePathRule (..), RewriteRule (..),
                 RulePattern (..) )
import qualified Kore.Step.Rule as RulePattern
import           Kore.Step.Simplification.Data
                 ( MonadSimplify, SimplifierVariable )
import           Kore.Step.Simplification.Pattern
                 ( simplifyAndRemoveTopExists )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import qualified Kore.Step.Step as Step
import           Kore.Step.Strategy
                 ( Strategy )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Strategies.ProofState
import qualified Kore.Strategies.ProofState as Goal
import           Kore.Syntax.Variable
                 ( SortedVariable, Variable )
import           Kore.TopBottom
                 ( isBottom )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse, unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )
import           Kore.Variables.UnifiedVariable
                 ( UnifiedVariable (ElemVar), isElemVar )

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

-- TODO: default derivePar and deriveSeq are identical except for the
-- rule application function called
class Goal goal where
    data Rule goal

    proofStrategy
        :: [goal]
        -> [Rule goal]
        -> [Strategy (Prim (Rule goal))]

    -- | Remove the destination of the goal.
    removeDestination
        :: MonadSimplify m
        => goal
        -> Strategy.TransitionT (Rule goal) m goal
    default removeDestination
        :: MonadSimplify m
        => SimplifierVariable variable
        => Coercible goal (RulePattern variable)
        => goal
        -> Strategy.TransitionT (Rule goal) m goal
    removeDestination goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
            removal = removalPredicate destination configuration
            result = Conditional.andPredicate configuration removal
        pure $ makeRuleFromPatterns result destination

    simplify
        :: MonadSimplify m
        => goal
        -> Strategy.TransitionT (Rule goal) m goal
    default simplify
        :: MonadSimplify m
        => SimplifierVariable variable
        => Coercible goal (RulePattern variable)
        => goal
        -> Strategy.TransitionT (Rule goal) m goal
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
                        fmap (`makeRuleFromPatterns` destination) filteredConfigs
                Foldable.asum (pure <$> simplifiedRules)

    isTriviallyValid :: goal -> Bool
    default isTriviallyValid
        :: SimplifierVariable variable
        => Coercible goal (RulePattern variable)
        => goal -> Bool
    isTriviallyValid = isBottom . RulePattern.left . coerce

    isTrusted :: goal -> Bool
    default isTrusted
        :: SimplifierVariable variable
        => Coercible goal (RulePattern variable)
        => goal -> Bool
    isTrusted =
        Attribute.Trusted.isTrusted
        . Attribute.Axiom.trusted
        . RulePattern.attributes
        . coerce

    -- | Apply 'Rule's to the goal in parallel.
    derivePar
        :: MonadSimplify m
        => [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)
    default derivePar
        :: forall m variable
        .  MonadSimplify m
        => SimplifierVariable variable
        => Coercible goal (RulePattern variable)
        => Coercible (RulePattern variable) goal
        => Coercible (Rule goal) (RulePattern variable)
        => Coercible (RulePattern variable) (Rule goal)
        => [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)
    derivePar rules goal = do
        let destination = getDestination goal
            configuration :: Pattern variable
            configuration = getConfiguration goal
            rewrites = coerce <$> rules
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
                        $ coerce
                        . RewriteRule
                        . Step.unwrapRule
                        . Step.withoutUnification
                    traverseConfigs =
                        Result.traverseConfigs
                            (pure . Goal)
                            removeDestSimplifyRemainder
                let ruleResults =
                        Result.mapConfigs
                            (`makeRuleFromPatterns` destination)
                            (`makeRuleFromPatterns` destination)
                            (Result.mergeResults results)
                results' <-
                    traverseConfigs (mapRules ruleResults)
                Result.transitionResults results'

    -- | Apply 'Rule's to the goal in sequence.
    deriveSeq
        :: MonadSimplify m
        => [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)
    default deriveSeq
        :: forall m variable
        .  MonadSimplify m
        => SimplifierVariable variable
        => Coercible goal (RulePattern variable)
        => Coercible (RulePattern variable) goal
        => Coercible (Rule goal) (RulePattern variable)
        => Coercible (RulePattern variable) (Rule goal)
        => [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)
    deriveSeq rules goal = do
        let destination = getDestination goal
            configuration = getConfiguration goal
            rewrites = coerce <$> rules
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
                        $ coerce
                        . RewriteRule
                        . Step.unwrapRule
                        . Step.withoutUnification
                    traverseConfigs =
                        Result.traverseConfigs
                            (pure . Goal.Goal)
                            removeDestSimplifyRemainder
                let ruleResults =
                        Result.mapConfigs
                            (`makeRuleFromPatterns` destination)
                            (`makeRuleFromPatterns` destination)
                            (Result.mergeResults results)
                results' <-
                    traverseConfigs (mapRules ruleResults)
                Result.transitionResults results'

instance (SimplifierVariable variable) => Goal (OnePathRule variable) where
    newtype Rule (OnePathRule variable) =
        Rule { unRule :: RewriteRule variable }
        deriving (GHC.Generic, Show, Unparse)

    proofStrategy goals rules =
        makeProofStrategy OnePathStrategy coinductiveRewrites rewrites
      where
        coinductiveRewrites = fmap (Rule . RewriteRule . getOnePathRule) goals
        rewrites = rules

instance SOP.Generic (Rule (OnePathRule variable))

instance SOP.HasDatatypeInfo (Rule (OnePathRule variable))

instance Debug variable => Debug (Rule (OnePathRule variable))

instance (SimplifierVariable variable) => Goal (AllPathRule variable) where
    newtype Rule (AllPathRule variable) =
        ARule { unRule :: RewriteRule variable }
        deriving (GHC.Generic, Show, Unparse)

    proofStrategy goals rules =
        makeProofStrategy AllPathStrategy coinductiveRewrites rewrites
      where
        coinductiveRewrites = fmap (ARule . RewriteRule . getAllPathRule) goals
        rewrites = rules

instance SOP.Generic (Rule (AllPathRule variable))

instance SOP.HasDatatypeInfo (Rule (AllPathRule variable))

instance Debug variable => Debug (Rule (AllPathRule variable))

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

data ProofStrategy = OnePathStrategy | AllPathStrategy

makeProofStrategy
    :: ProofStrategy
    -> [rule]
    -- ^ Claims
    -> [rule]
    -- ^ Axioms
    -> [Strategy (Prim rule)]
makeProofStrategy proofStrategy claims axioms =
    firstStep : repeat nextStep
  where
    firstStep = firstStepStrategy proofStrategy axioms
    nextStep = nextStepStrategy proofStrategy claims axioms

firstStepStrategy
    :: ProofStrategy
    -> [rule]
    -- ^ Axioms
    -> Strategy (Prim rule)
firstStepStrategy proofStrategy axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRem
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , deriveSeqOrPar proofStrategy axioms
        , Simplify
        , TriviallyValid
        ]

nextStepStrategy
    :: ProofStrategy
    -> [rule]
    -- ^ Claims
    -> [rule]
    -- ^ Axioms
    -> Strategy (Prim rule)
nextStepStrategy proofStrategy claims axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRem
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq claims
        , deriveSeqOrPar proofStrategy axioms
        , Simplify
        , TriviallyValid
        ]

deriveSeqOrPar :: ProofStrategy -> [rule] -> Prim rule
deriveSeqOrPar proofStrategy rules =
    case proofStrategy of
        OnePathStrategy -> DeriveSeq rules
        AllPathStrategy -> DerivePar rules

allPathStrategy
    :: [rule]
    -- ^ Claims
    -> [rule]
    -- ^ Axioms
    -> [Strategy (Prim rule)]
allPathStrategy =
    makeProofStrategy AllPathStrategy

onePathStrategy
    :: [rule]
    -- ^ Claims
    -> [rule]
    -- ^ Axioms
    -> [Strategy (Prim rule)]
onePathStrategy =
    makeProofStrategy AllPathStrategy

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
    .  SimplifierVariable variable
    => Coercible (RulePattern variable) rule
    => Pattern variable
    -> Pattern variable
    -> rule
makeRuleFromPatterns configuration destination =
    let (left, Conditional.toPredicate -> requires) =
            Pattern.splitTerm configuration
        (right, Conditional.toPredicate -> ensures) =
            Pattern.splitTerm destination
    in coerce RulePattern
        { left, right, requires, ensures, attributes = Default.def }

{- | The predicate to remove the destination from the present configuration.
 -}
removalPredicate
    :: SimplifierVariable variable
    => Pattern variable
    -- ^ Destination
    -> Pattern variable
    -- ^ Current configuration
    -> Syntax.Predicate variable
removalPredicate destination config =
    let
        -- The variables of the destination that are missing from the
        -- configuration. These are the variables which should be existentially
        -- quantified in the removal predicate.
        configVariables =
            Attribute.FreeVariables.getFreeVariables
            $ Pattern.freeVariables config
        destinationVariables =
            Attribute.FreeVariables.getFreeVariables
            $ Pattern.freeVariables destination
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

removeDestSimplifyRemainder
    :: forall m goal rule
    .  MonadSimplify m
    => Goal goal
    => rule ~ Rule goal
    => goal
    -> Strategy.TransitionT
        rule
        m
        (Goal.ProofState goal)
removeDestSimplifyRemainder remainder = do
    result <- removeDestination remainder >>= simplify
    if isTriviallyValid result
       then pure Goal.Proven
       else pure . Goal.GoalRem $ result
