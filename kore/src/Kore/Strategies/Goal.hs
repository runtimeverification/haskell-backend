{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.Goal
    ( Goal (..)
    , TransitionRule
    , Prim
    , FromRulePattern (..)
    , ClaimExtractor (..)
    , WithConfiguration (..)
    , CheckImplicationResult (..)
    , extractClaims
    , unprovenNodes
    , proven
    , onePathFirstStep
    , onePathFollowupStep
    , allPathFirstStep
    , allPathFollowupStep
    , getConfiguration
    , getDestination
    , transitionRule
    , isTrusted
    , removalPatterns
    -- * Re-exports
    , module Kore.Strategies.Rule
    , module Kore.Log.InfoReachability
    ) where

import Prelude.Kore

import Control.Error
    ( ExceptT
    , runExceptT
    , throwE
    )
import Control.Lens
    ( Lens'
    )
import qualified Control.Lens as Lens
import Control.Monad
    ( foldM
    )
import Control.Monad.Catch
    ( Exception (..)
    , SomeException (..)
    )
import Data.Coerce
    ( Coercible
    , coerce
    )
import qualified Data.Foldable as Foldable
import Data.Functor.Compose
import Data.Generics.Product
    ( field
    )
import Data.Generics.Wrapped
    ( _Unwrapped
    )
import Data.Stream.Infinite
    ( Stream (..)
    )
import qualified Data.Stream.Infinite as Stream

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import Kore.Attribute.Pattern.FreeVariables
    ( freeVariables
    )
import qualified Kore.Attribute.Trusted as Attribute.Trusted
import Kore.IndexedModule.IndexedModule
    ( IndexedModule (indexedModuleClaims)
    , VerifiedModule
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( isFunctionPattern
    , mkIn
    , termLikeSort
    )
import Kore.Log.InfoReachability
import qualified Kore.Profiler.Profile as Profile
    ( timeStrategy
    )
import Kore.Rewriting.RewritingVariable
import Kore.Step.Result
    ( Result (..)
    , Results (..)
    )
import qualified Kore.Step.RewriteStep as Step
import Kore.Step.Rule
    ( QualifiedAxiomPattern (..)
    , fromSentenceAxiom
    )
import Kore.Step.RulePattern
    ( AllPathRule (..)
    , FromRulePattern (..)
    , OnePathRule (..)
    , RHS
    , ReachabilityRule (..)
    , RewriteRule (..)
    , RulePattern (..)
    , ToRulePattern (..)
    , ToRulePattern (..)
    , topExistsToImplicitForall
    )
import qualified Kore.Step.RulePattern as RulePattern
import Kore.Step.Simplification.AndPredicates
    ( simplifyEvaluatedMultiPredicate
    )
import qualified Kore.Step.Simplification.Condition as Condition
import Kore.Step.Simplification.Data
    ( InternalVariable
    , MonadSimplify
    )
import qualified Kore.Step.Simplification.Exists as Exists
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.OrPattern
    ( simplifyConditionsWithSmt
    )
import Kore.Step.Simplification.Pattern
    ( simplifyTopConfiguration
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import qualified Kore.Step.Step as Step
import Kore.Step.Strategy
    ( Strategy
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Step.Transition
    ( tryTransitionT
    )
import qualified Kore.Step.Transition as Transition
import Kore.Strategies.ProofState hiding
    ( proofState
    )
import qualified Kore.Strategies.ProofState as ProofState
import Kore.Strategies.Rule
import qualified Kore.Syntax.Sentence as Syntax
import Kore.Syntax.Variable
import Kore.TopBottom
    ( isBottom
    , isTop
    )
import qualified Kore.Unification.Procedure as Unification
import Kore.Unparser
    ( unparse
    )
import qualified Kore.Verified as Verified
import qualified Pretty

{- | The final nodes of an execution graph which were not proven.

See also: 'Strategy.pickFinal', 'extractUnproven'

 -}
unprovenNodes
    :: forall goal a
    .  Strategy.ExecutionGraph (ProofState a) (Rule goal)
    -> MultiOr.MultiOr a
unprovenNodes executionGraph =
    MultiOr.MultiOr
    $ mapMaybe extractUnproven
    $ Strategy.pickFinal executionGraph

{- | Does the 'Strategy.ExecutionGraph' indicate a successful proof?
 -}
proven
    :: forall goal a
    .  Strategy.ExecutionGraph (ProofState a) (Rule goal)
    -> Bool
proven = Foldable.null . unprovenNodes

class Goal goal where
    goalToRule :: goal -> Rule goal
    default goalToRule
        :: Coercible goal (Rule goal)
        => goal -> Rule goal
    goalToRule = coerce

    strategy
        :: goal
        -> [goal]
        -> [Rule goal]
        -> Stream (Strategy Prim)

    isTriviallyValid :: goal -> Bool

    checkImplication
        :: MonadSimplify m
        => goal -> m (CheckImplicationResult goal)

    simplify
        :: MonadSimplify m
        => goal
        -> Strategy.TransitionT (Rule goal) m goal

    {- TODO (thomas.tuegel): applyClaims and applyAxioms should return:

    > data ApplyResult goal
    >     = ApplyRewritten !goal
    >     | ApplyRemainder !goal

    Rationale: ProofState is part of the implementation of transitionRule, that
    is: these functions have hidden knowledge of how transitionRule works
    because they tell it what to do next. Instead, they should report their
    result and leave the decision up to transitionRule.

    -}
    applyClaims
        :: MonadSimplify m
        => [goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)

    applyAxioms
        :: MonadSimplify m
        => [[Rule goal]]
        -> goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)

type AxiomAttributes = Attribute.Axiom.Axiom Symbol VariableName

class ClaimExtractor claim where
    extractClaim :: (AxiomAttributes, Verified.SentenceClaim) -> Maybe claim

-- | Extracts all One-Path claims from a verified module.
extractClaims
    :: ClaimExtractor claim
    => VerifiedModule declAtts
    -- ^ 'IndexedModule' containing the definition
    -> [claim]
extractClaims = mapMaybe extractClaim . indexedModuleClaims

{- NOTE: Non-deterministic semantics

The current implementation of one-path verification assumes that the proof goal
is deterministic, that is: the proof goal would not be discharged during at a
non-confluent state in the execution of a non-deterministic semantics. (Often
this means that the definition is simply deterministic.) As a result, given the
non-deterministic definition

> module ABC
>   import DOMAINS
>   syntax S ::= "a" | "b" | "c"
>   rule [ab]: a => b
>   rule [ac]: a => c
> endmodule

this claim would be provable,

> rule a => b [claim]

but this claim would **not** be provable,

> rule a => c [claim]

because the algorithm would first apply semantic rule [ab], which prevents rule
[ac] from being used.

We decided to assume that the definition is deterministic because one-path
verification is mainly used only for deterministic semantics and the assumption
simplifies the implementation. However, this assumption is not an essential
feature of the algorithm. You should not rely on this assumption elsewhere. This
decision is subject to change without notice.

This instance contains the default implementation for a one-path strategy. You can apply it to the
first two arguments and pass the resulting function to 'Kore.Strategies.Verification.verify'.

Things to note when implementing your own:

1. The first step does not use the reachability claims

2. You can return an infinite list.
-}

instance Goal OnePathRule where
    goalToRule =
        OnePathRewriteRule
        . mkRewritingRule
        . RewriteRule
        . getOnePathRule

    simplify = simplify' _Unwrapped

    checkImplication = checkImplication' _Unwrapped

    applyClaims claims = deriveSeqOnePath (map goalToRule claims)

    applyAxioms axioms = deriveSeqOnePath (concat axioms)

    isTriviallyValid = isTriviallyValid' _Unwrapped

    strategy _ _ _ = onePathFirstStep :> Stream.iterate id onePathFollowupStep

deriveSeqOnePath
    ::  MonadSimplify simplifier
    =>  [Rule OnePathRule]
    ->  OnePathRule
    ->  Strategy.TransitionT (Rule OnePathRule) simplifier
            (ProofState OnePathRule)
deriveSeqOnePath rules =
    deriveSeq' _Unwrapped OnePathRewriteRule rewrites
  where
    rewrites = unRuleOnePath <$> rules

instance ClaimExtractor OnePathRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (OnePathClaimPattern claim) -> Just claim
            _ -> Nothing

instance Goal AllPathRule where
    goalToRule =
        AllPathRewriteRule
        . mkRewritingRule
        . RewriteRule
        . getAllPathRule

    simplify = simplify' _Unwrapped
    checkImplication = checkImplication' _Unwrapped
    isTriviallyValid = isTriviallyValid' _Unwrapped
    applyClaims claims = deriveSeqAllPath (map goalToRule claims)

    applyAxioms axiomss = \goal ->
        foldM applyAxioms1 (GoalRemainder goal) axiomss
      where
        applyAxioms1 proofState axioms
          | Just goal <- retractRewritableGoal proofState =
            deriveParAllPath axioms goal
            >>= simplifyRemainder
            >>= checkTriviallyValid
          | otherwise =
            pure proofState

        retractRewritableGoal (Goal goal) = Just goal
        retractRewritableGoal (GoalRemainder goal) = Just goal
        retractRewritableGoal _ = Nothing

        simplifyRemainder proofState =
            case proofState of
                GoalRemainder goal -> GoalRemainder <$> simplify goal
                _ -> return proofState

        checkTriviallyValid proofState
          | all isTriviallyValid proofState = pure Proven
          | otherwise = pure proofState

    strategy _ _ _ = allPathFirstStep :> Stream.iterate id allPathFollowupStep

deriveParAllPath
    ::  MonadSimplify simplifier
    =>  [Rule AllPathRule]
    ->  AllPathRule
    ->  Strategy.TransitionT (Rule AllPathRule) simplifier
            (ProofState AllPathRule)
deriveParAllPath rules =
    derivePar' _Unwrapped AllPathRewriteRule rewrites
  where
    rewrites = unRuleAllPath <$> rules

deriveSeqAllPath
    ::  MonadSimplify simplifier
    =>  [Rule AllPathRule]
    ->  AllPathRule
    ->  Strategy.TransitionT (Rule AllPathRule) simplifier
            (ProofState AllPathRule)
deriveSeqAllPath rules =
    deriveSeq' _Unwrapped AllPathRewriteRule rewrites
  where
    rewrites = unRuleAllPath <$> rules

instance ClaimExtractor AllPathRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (AllPathClaimPattern claim) -> Just claim
            _ -> Nothing

instance Goal ReachabilityRule where
    goalToRule (OnePath rule) =
        ReachabilityRewriteRule
        $ mkRewritingRule
        $ RewriteRule
        $ getOnePathRule rule
    goalToRule (AllPath rule) =
        ReachabilityRewriteRule
        $ mkRewritingRule
        $ RewriteRule
        $ getAllPathRule rule

    simplify (AllPath goal) = allPathTransition $ AllPath <$> simplify goal
    simplify (OnePath goal) = onePathTransition $ OnePath <$> simplify goal

    checkImplication (AllPath goal) = fmap AllPath <$> checkImplication goal
    checkImplication (OnePath goal) = fmap OnePath <$> checkImplication goal

    isTriviallyValid (AllPath goal) = isTriviallyValid goal
    isTriviallyValid (OnePath goal) = isTriviallyValid goal

    applyClaims claims (AllPath goal) =
        applyClaims (mapMaybe maybeAllPath claims) goal
        & fmap (fmap AllPath)
        & allPathTransition
    applyClaims claims (OnePath goal) =
        applyClaims (mapMaybe maybeOnePath claims) goal
        & fmap (fmap OnePath)
        & onePathTransition

    applyAxioms axiomGroups (AllPath goal) =
        applyAxioms (coerce axiomGroups) goal
        & fmap (fmap AllPath)
        & allPathTransition
    applyAxioms axiomGroups (OnePath goal) =
        applyAxioms (coerce axiomGroups) goal
        & fmap (fmap OnePath)
        & onePathTransition

    strategy
        :: ReachabilityRule
        -> [ReachabilityRule]
        -> [Rule ReachabilityRule]
        -> Stream (Strategy Prim)
    strategy goal claims axioms =
        case goal of
            OnePath rule ->
                strategy
                    rule
                    (mapMaybe maybeOnePath claims)
                    (fmap ruleReachabilityToRuleOnePath axioms)
            AllPath rule ->
                strategy
                    rule
                    (mapMaybe maybeAllPath claims)
                    (fmap ruleReachabilityToRuleAllPath axioms)

instance ClaimExtractor ReachabilityRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (OnePathClaimPattern claim) -> Just (OnePath claim)
            Right (AllPathClaimPattern claim) -> Just (AllPath claim)
            _ -> Nothing

allPathTransition
    :: Monad m
    => Strategy.TransitionT (Rule AllPathRule) m a
    -> Strategy.TransitionT (Rule ReachabilityRule) m a
allPathTransition = Transition.mapRules ruleAllPathToRuleReachability

onePathTransition
    :: Monad m
    => Strategy.TransitionT (Rule OnePathRule) m a
    -> Strategy.TransitionT (Rule ReachabilityRule) m a
onePathTransition = Transition.mapRules ruleOnePathToRuleReachability

maybeOnePath :: ReachabilityRule -> Maybe OnePathRule
maybeOnePath (OnePath rule) = Just rule
maybeOnePath _ = Nothing

maybeAllPath :: ReachabilityRule -> Maybe AllPathRule
maybeAllPath (AllPath rule) = Just rule
maybeAllPath _ = Nothing

-- The functions below are easier to read coercions between
-- the newtypes over 'RewriteRule VariableName' defined in the
-- instances of 'Goal' as 'Rule's.
ruleReachabilityToRuleAllPath
    :: Rule ReachabilityRule
    -> Rule AllPathRule
ruleReachabilityToRuleAllPath = coerce

ruleReachabilityToRuleOnePath
    :: Rule ReachabilityRule
    -> Rule OnePathRule
ruleReachabilityToRuleOnePath = coerce

ruleAllPathToRuleReachability
    :: Rule AllPathRule
    -> Rule ReachabilityRule
ruleAllPathToRuleReachability = coerce

ruleOnePathToRuleReachability
    :: Rule OnePathRule
    -> Rule ReachabilityRule
ruleOnePathToRuleReachability = coerce

type TransitionRule m goal =
    Prim
    -> ProofState goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal)

transitionRule
    :: forall m goal
    .  MonadSimplify m
    => Goal goal
    => [goal]
    -> [[Rule goal]]
    -> TransitionRule m goal
transitionRule claims axiomGroups = transitionRuleWorker
  where
    transitionRuleWorker
        :: Prim
        -> ProofState goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal)
    transitionRuleWorker CheckProven Proven = empty
    transitionRuleWorker CheckGoalRemainder (GoalRemainder _) = empty

    transitionRuleWorker ResetGoal (GoalRewritten goal) =
        return (Goal goal)

    transitionRuleWorker CheckGoalStuck (GoalStuck _) = empty

    transitionRuleWorker Simplify (Goal goal) =
        Profile.timeStrategy "Goal.Simplify" $ do
            results <- tryTransitionT (simplify goal)
            case results of
                [] -> return Proven
                _  -> Goal <$> Transition.scatter results

    transitionRuleWorker Simplify (GoalRemainder goal) =
        Profile.timeStrategy "Goal.SimplifyRemainder"
        $ GoalRemainder <$> simplify goal

    transitionRuleWorker CheckImplication (Goal goal) =
        Profile.timeStrategy "Goal.CheckImplication" $ do
            result <- checkImplication goal
            case result of
                NotImpliedStuck a -> pure (GoalStuck a)
                Implied -> pure Proven
                NotImplied a -> pure (Goal a)
    transitionRuleWorker CheckImplication (GoalRemainder goal) =
        Profile.timeStrategy "Goal.CheckImplicationRemainder" $ do
            result <- checkImplication goal
            case result of
                NotImpliedStuck a -> pure (GoalStuck a)
                Implied -> pure Proven
                NotImplied a -> pure (GoalRemainder a)

    transitionRuleWorker TriviallyValid (Goal goal)
      | isTriviallyValid goal =
          return Proven
    transitionRuleWorker TriviallyValid (GoalRemainder goal)
      | isTriviallyValid goal =
          return Proven
    transitionRuleWorker TriviallyValid (GoalRewritten goal)
      | isTriviallyValid goal =
          return Proven

    -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
    --
    -- thomas.tuegel: "Here" is in ApplyClaims and ApplyAxioms.
    --
    -- Note that in most transitions it is obvious what is being transformed
    -- into what, e.g. that a `ResetGoal` transition transforms
    -- `GoalRewritten` into `Goal`. However, here we're taking a `Goal`
    -- and transforming it into `GoalRewritten` and `GoalRemainder` in an
    -- opaque way. I think that there's no good reason for wrapping the
    -- results in `derivePar` as opposed to here.

    transitionRuleWorker ApplyClaims (Goal goal) =
        Profile.timeStrategy "applyClaims"
        $ applyClaims claims goal

    transitionRuleWorker ApplyClaims (GoalRemainder goal) =
        Profile.timeStrategy "applyClaims"
        $ applyClaims claims goal

    transitionRuleWorker ApplyAxioms (Goal goal) =
        Profile.timeStrategy "applyAxioms"
        $ applyAxioms axiomGroups goal

    transitionRuleWorker ApplyAxioms (GoalRemainder goal) =
        Profile.timeStrategy "applyAxioms"
        $ applyAxioms axiomGroups goal

    transitionRuleWorker _ state = return state

onePathFirstStep :: Strategy Prim
onePathFirstStep =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalStuck
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , CheckImplication
        , ApplyAxioms
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

onePathFollowupStep :: Strategy Prim
onePathFollowupStep =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalStuck
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , CheckImplication
        , ApplyClaims
        , ApplyAxioms
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

allPathFirstStep :: Strategy Prim
allPathFirstStep =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalStuck
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , CheckImplication
        , ApplyAxioms
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

allPathFollowupStep :: Strategy Prim
allPathFollowupStep =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalStuck
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , CheckImplication
        , ApplyClaims
        , ApplyAxioms
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

{- | The result of checking the direct implication of a proof goal.

As an optimization, 'checkImplication' returns 'NotImpliedStuck' when the
implication between /terms/ is valid, but the implication between side
conditions does not hold.

 -}
data CheckImplicationResult a
    = Implied
    -- ^ The implication is valid.
    | NotImplied !a
    -- ^ The implication is not valid.
    | NotImpliedStuck !a
    -- ^ The implication between /terms/ is valid, but the implication between
    -- side-conditions is not valid.
    deriving (Functor)

-- | Remove the destination of the goal.
checkImplication'
    :: forall goal m
    .  MonadSimplify m
    => Lens' goal (RulePattern VariableName)
    -> goal
    -> m (CheckImplicationResult goal)
checkImplication' lensRulePattern goal =
    goal
    & Lens.traverseOf lensRulePattern (Compose . checkImplicationWorker)
    & getCompose
  where
    checkImplicationWorker
        :: RulePattern VariableName
        -> m (CheckImplicationResult (RulePattern VariableName))
    checkImplicationWorker (snd . Step.refreshRule mempty -> rulePattern) =
        do
            removal <- removalPatterns destination configuration existentials
            when (isTop removal) (succeed . NotImplied $ rulePattern)
            let configAndRemoval = fmap (configuration <*) removal
                sideCondition =
                    Pattern.withoutTerm configuration
                    & SideCondition.fromCondition
            simplifiedRemoval <-
                simplifyConditionsWithSmt
                    sideCondition
                    configAndRemoval
            when (isBottom simplifiedRemoval) (succeed Implied)
            let stuckConfiguration = OrPattern.toPattern simplifiedRemoval
            rulePattern
                & Lens.set RulePattern.leftPattern stuckConfiguration
                & NotImpliedStuck
                & pure
        & run
      where
        configuration = Lens.view RulePattern.leftPattern rulePattern
        configFreeVars = freeVariables configuration
        destination =
            Lens.view (field @"rhs") rulePattern
            & topExistsToImplicitForall configFreeVars
        existentials =
            Lens.view (field @"existentials")
            . Lens.view (field @"rhs")
            $ rulePattern

        succeed :: r -> ExceptT r m a
        succeed = throwE

        run :: ExceptT r m r -> m r
        run acts = runExceptT acts >>= either pure pure

simplify'
    :: MonadSimplify m
    => Lens' goal (RulePattern VariableName)
    -> goal
    -> Strategy.TransitionT (Rule goal) m goal
simplify' lensRulePattern =
    Lens.traverseOf (lensRulePattern . RulePattern.leftPattern) $ \config -> do
        configs <-
            simplifyTopConfiguration config >>= SMT.Evaluator.filterMultiOr
            & lift
        if isBottom configs
            then pure Pattern.bottom
            else Foldable.asum (pure <$> configs)

isTriviallyValid' :: Lens' goal (RulePattern variable) -> goal -> Bool
isTriviallyValid' lensRulePattern =
    isBottom . RulePattern.left . Lens.view lensRulePattern

isTrusted :: From goal Attribute.Axiom.Trusted => goal -> Bool
isTrusted = Attribute.Trusted.isTrusted . from @_ @Attribute.Axiom.Trusted

-- | Exception that contains the last configuration before the error.
data WithConfiguration = WithConfiguration (Pattern VariableName) SomeException
    deriving (Show, Typeable)

instance Exception WithConfiguration

-- | Apply 'Rule's to the goal in parallel.
derivePar'
    :: forall m goal
    .  MonadSimplify m
    => Lens' goal (RulePattern VariableName)
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal)
derivePar' lensRulePattern mkRule =
    deriveWith lensRulePattern mkRule
    $ Step.applyRewriteRulesParallel Unification.unificationProcedure

type Deriver monad =
        [RewriteRule RewritingVariableName]
    ->  Pattern VariableName
    ->  monad (Step.Results RulePattern VariableName)

-- | Apply 'Rule's to the goal in parallel.
deriveWith
    :: forall m goal
    .  Monad m
    => Lens' goal (RulePattern VariableName)
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> Deriver m
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal)
deriveWith lensRulePattern mkRule takeStep rewrites goal =
    getCompose
    $ Lens.forOf lensRulePattern goal
    $ \rulePattern ->
        fmap (snd . Step.refreshRule mempty)
        $ Lens.forOf RulePattern.leftPattern rulePattern
        $ \config -> Compose $ do
            results <- takeStep rewrites config & lift
            deriveResults mkRule results

-- | Apply 'Rule's to the goal in sequence.
deriveSeq'
    :: forall m goal
    .  MonadSimplify m
    => Lens' goal (RulePattern VariableName)
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal)
deriveSeq' lensRulePattern mkRule =
    deriveWith lensRulePattern mkRule . flip
    $ Step.applyRewriteRulesSequence Unification.unificationProcedure

deriveResults
    :: (RewriteRule RewritingVariableName -> Rule goal)
    -> Step.Results RulePattern VariableName
    -> Strategy.TransitionT (Rule goal) simplifier
        (ProofState.ProofState (Pattern VariableName))
-- TODO (thomas.tuegel): Remove goal argument.
deriveResults mkRule Results { results, remainders } =
    addResults <|> addRemainders
  where
    addResults = Foldable.asum (addResult <$> results)
    addRemainders = Foldable.asum (addRemainder <$> Foldable.toList remainders)

    addResult Result { appliedRule, result } = do
        addRule appliedRule
        case Foldable.toList result of
            []      ->
                -- If the rule returns \bottom, the goal is proven on the
                -- current branch.
                pure Proven
            configs -> Foldable.asum (addRewritten <$> configs)

    addRewritten = pure . GoalRewritten
    addRemainder = pure . GoalRemainder

    addRule = Transition.addRule . fromAppliedRule

    fromAppliedRule = mkRule . RewriteRule . Step.withoutUnification

{- | The predicate to remove the destination from the present configuration.
 -}
removalPatterns
    :: forall variable m
    .  HasCallStack
    => InternalVariable variable
    => MonadSimplify m
    => Pattern variable
    -- ^ Destination
    -> Pattern variable
    -- ^ Current configuration
    -> [ElementVariable variable]
    -- ^ existentially quantified variables
    -> m (OrPattern variable)
removalPatterns
    destination
    configuration
    existentials
  | isFunctionPattern configTerm
  , isFunctionPattern destTerm
  = do
    unifiedConfigs <-
        mkIn configSort configTerm destTerm
        & Pattern.fromTermLike
        & Pattern.simplify sideCondition
    if isBottom unifiedConfigs
        then return OrPattern.top
        else do
            let unifiedConditions =
                    fmap Conditional.withoutTerm unifiedConfigs
            -- TODO (thomas.tuegel): Move this up to avoid repeated calls.
            destinationConditions <-
                Conditional.withoutTerm destination
                & Condition.simplifyCondition sideCondition
                & OrCondition.observeAllT
            remainderConditions <-
                simplifyEvaluatedMultiPredicate
                    sideCondition
                    (MultiAnd.make
                        [ unifiedConditions
                        , destinationConditions
                        ]
                    )
            let remainderPatterns =
                    fmap Pattern.fromCondition_ remainderConditions
            existentialRemainders <-
                foldM
                    (Exists.simplifyEvaluated sideCondition & flip)
                    remainderPatterns
                    existentials
            Not.simplifyEvaluated sideCondition existentialRemainders
  | otherwise =
      error . show . Pretty.vsep $
          [ "The remove destination step expects\
          \ the configuration and the destination terms\
          \ to be function-like."
          , Pretty.indent 2 "Configuration term:"
          , Pretty.indent 4 (unparse configTerm)
          , Pretty.indent 2 "Destination term:"
          , Pretty.indent 4 (unparse destTerm)
          ]
  where
    Conditional { term = destTerm } = destination
    (configTerm, configPredicate) = Pattern.splitTerm configuration
    sideCondition = SideCondition.assumeTrueCondition configPredicate
    configSort = termLikeSort configTerm

getConfiguration :: ReachabilityRule -> Pattern VariableName
getConfiguration (toRulePattern -> RulePattern { left, requires }) =
    Pattern.withCondition left (Conditional.fromPredicate requires)

getDestination :: ReachabilityRule -> RHS VariableName
getDestination (toRulePattern -> RulePattern { rhs }) = rhs
