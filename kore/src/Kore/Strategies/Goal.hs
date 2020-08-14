{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.Goal
    ( Goal (..)
    , AppliedRule (..)
    , strategy
    , TransitionRule
    , Prim
    , ClaimExtractor (..)
    , WithConfiguration (..)
    , CheckImplicationResult (..)
    , extractClaims
    , unprovenNodes
    , proven
    , reachabilityFirstStep
    , reachabilityNextStep
    , transitionRule
    , isTrusted
    -- * Re-exports
    , module Kore.Strategies.Rule
    , module Kore.Log.InfoReachability
    , getConfiguration
    , getDestination
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
    ( coerce
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
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Label as Attribute
    ( Label
    )
import qualified Kore.Attribute.RuleIndex as Attribute
    ( RuleIndex
    )
import qualified Kore.Attribute.SourceLocation as Attribute
    ( SourceLocation
    )
import qualified Kore.Attribute.Trusted as Attribute.Trusted
import Kore.IndexedModule.IndexedModule
    ( IndexedModule (indexedModuleClaims)
    , VerifiedModule
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.MultiOr
    ( MultiOr
    )
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
import Kore.Internal.Predicate
    ( makeCeilPredicate_
    )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( TermLike
    , isFunctionPattern
    , mkDefined
    , mkIn
    , termLikeSort
    )
import Kore.Log.InfoReachability
import Kore.Log.WarnStuckProofState
    ( warnStuckProofStateTermsNotUnifiable
    , warnStuckProofStateTermsUnifiable
    )
import Kore.Rewriting.RewritingVariable
import Kore.Step.ClaimPattern
    ( AllPathRule (..)
    , ClaimPattern (..)
    , OnePathRule (..)
    , ReachabilityRule (..)
    , getConfiguration
    , getDestination
    )
import qualified Kore.Step.ClaimPattern as ClaimPattern
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
    ( RulePattern (..)
    )
import Kore.Step.Simplification.AndPredicates
    ( simplifyEvaluatedMultiPredicate
    )
import qualified Kore.Step.Simplification.Condition as Condition
import Kore.Step.Simplification.Data
    ( MonadSimplify
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
    )
import qualified Kore.Unification.Procedure as Unification
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Kore.Verified as Verified
import Logic
    ( LogicT
    )
import qualified Logic
import qualified Pretty

{- | The final nodes of an execution graph which were not proven.

See also: 'Strategy.pickFinal', 'extractUnproven'

 -}
unprovenNodes
    :: forall goal a
    .  Strategy.ExecutionGraph (ProofState a) (AppliedRule goal)
    -> MultiOr.MultiOr a
unprovenNodes executionGraph =
    MultiOr.MultiOr
    $ mapMaybe extractUnproven
    $ Strategy.pickFinal executionGraph

{- | Does the 'Strategy.ExecutionGraph' indicate a successful proof?
 -}
proven
    :: forall goal a
    .  Strategy.ExecutionGraph (ProofState a) (AppliedRule goal)
    -> Bool
proven = Foldable.null . unprovenNodes

class Goal goal where
    -- TODO (thomas.tuegel): isTriviallyValid should be part of
    -- checkImplication.
    isTriviallyValid :: goal -> Bool

    checkImplication
        :: MonadSimplify m
        => goal -> m (CheckImplicationResult goal)

    simplify
        :: MonadSimplify m
        => goal
        -> Strategy.TransitionT (AppliedRule goal) m goal

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
        -> Strategy.TransitionT (AppliedRule goal) m (ProofState goal)

    applyAxioms
        :: MonadSimplify m
        => [[Rule goal]]
        -> goal
        -> Strategy.TransitionT (AppliedRule goal) m (ProofState goal)

data AppliedRule goal
    = AppliedAxiom (Rule goal)
    | AppliedClaim goal
    deriving (GHC.Generic)

instance SOP.Generic goal => SOP.Generic (AppliedRule goal)

instance SOP.HasDatatypeInfo goal => SOP.HasDatatypeInfo (AppliedRule goal)

instance
    ( Debug goal
    , SOP.HasDatatypeInfo goal
    , Debug (Rule goal)
    , SOP.HasDatatypeInfo (Rule goal)
    ) => Debug (AppliedRule goal)

instance
    ( Diff goal
    , Debug goal
    , SOP.HasDatatypeInfo goal
    , Diff (Rule goal)
    , Debug (Rule goal)
    , SOP.HasDatatypeInfo (Rule goal)
    ) => Diff (AppliedRule goal)

instance (From goal Attribute.Label, From (Rule goal) Attribute.Label)
  => From (AppliedRule goal) Attribute.Label
  where
    from (AppliedAxiom rule) = from rule
    from (AppliedClaim goal) = from goal

instance (From goal Attribute.RuleIndex, From (Rule goal) Attribute.RuleIndex)
  => From (AppliedRule goal) Attribute.RuleIndex
  where
    from (AppliedAxiom rule) = from rule
    from (AppliedClaim goal) = from goal

instance (From goal Attribute.SourceLocation, From (Rule goal) Attribute.SourceLocation)
  => From (AppliedRule goal) Attribute.SourceLocation
  where
    from (AppliedAxiom rule) = from rule
    from (AppliedClaim goal) = from goal

instance (Unparse goal, Unparse (Rule goal)) => Unparse (AppliedRule goal)
  where
    unparse (AppliedAxiom rule) = unparse rule
    unparse (AppliedClaim goal) = unparse goal

    unparse2 (AppliedAxiom rule) = unparse2 rule
    unparse2 (AppliedClaim goal) = unparse2 goal

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

This instance contains the default implementation for a one-path strategy. You
can apply it to the first two arguments and pass the resulting function to
'Kore.Strategies.Verification.verify'.

Things to note when implementing your own:

1. The first step does not use the reachability claims

2. You can return an infinite list.
-}

instance Goal OnePathRule where
    simplify = simplify' _Unwrapped

    checkImplication = checkImplication' _Unwrapped

    applyClaims claims = deriveSeqClaim _Unwrapped OnePathRule claims

    applyAxioms axioms = deriveSeqAxiomOnePath (concat axioms)

    isTriviallyValid = isTriviallyValid' _Unwrapped

deriveSeqClaim
    :: MonadSimplify m
    => Step.UnifyingRule goal
    => Step.UnifyingRuleVariable goal ~ RewritingVariableName
    => From goal (TermLike RewritingVariableName)
    => From goal Attribute.SourceLocation
    => Lens' goal ClaimPattern
    -> (ClaimPattern -> goal)
    -> [goal]
    -> goal
    -> Strategy.TransitionT (AppliedRule goal) m (ProofState goal)
deriveSeqClaim lensClaimPattern mkClaim claims goal =
    getCompose
    $ Lens.forOf lensClaimPattern goal
    $ \claimPattern ->
        fmap (snd . Step.refreshRule mempty)
        $ Lens.forOf (field @"left") claimPattern
        $ \config -> Compose $ do
            results <-
                Step.applyClaimsSequence
                    mkClaim
                    Unification.unificationProcedure
                    config
                    (Lens.view lensClaimPattern <$> claims)
                    & lift
            deriveResults fromAppliedRule results
  where
    fromAppliedRule =
        AppliedClaim
        . mkClaim
        . Step.withoutUnification

deriveSeqAxiomOnePath
    ::  MonadSimplify simplifier
    =>  [Rule OnePathRule]
    ->  OnePathRule
    ->  Strategy.TransitionT (AppliedRule OnePathRule) simplifier
            (ProofState OnePathRule)
deriveSeqAxiomOnePath rules =
    deriveSeq' _Unwrapped OnePathRewriteRule rewrites
  where
    rewrites = unRuleOnePath <$> rules

instance ClaimExtractor OnePathRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (OnePathClaimPattern claim) -> Just claim
            _ -> Nothing

instance Goal AllPathRule where
    simplify = simplify' _Unwrapped
    checkImplication = checkImplication' _Unwrapped
    isTriviallyValid = isTriviallyValid' _Unwrapped
    applyClaims claims = deriveSeqClaim _Unwrapped AllPathRule claims

    applyAxioms axiomss = \goal ->
        foldM applyAxioms1 (GoalRemainder goal) axiomss
      where
        applyAxioms1 proofState axioms
          | Just goal <- retractRewritableGoal proofState =
            deriveParAxiomAllPath axioms goal
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


deriveParAxiomAllPath
    ::  MonadSimplify simplifier
    =>  [Rule AllPathRule]
    ->  AllPathRule
    ->  Strategy.TransitionT (AppliedRule AllPathRule) simplifier
            (ProofState AllPathRule)
deriveParAxiomAllPath rules =
    derivePar' _Unwrapped AllPathRewriteRule rewrites
  where
    rewrites = unRuleAllPath <$> rules

instance ClaimExtractor AllPathRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (AllPathClaimPattern claim) -> Just claim
            _ -> Nothing

instance Goal ReachabilityRule where
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

instance ClaimExtractor ReachabilityRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (OnePathClaimPattern claim) -> Just (OnePath claim)
            Right (AllPathClaimPattern claim) -> Just (AllPath claim)
            _ -> Nothing

allPathTransition
    :: Monad m
    => Strategy.TransitionT (AppliedRule AllPathRule) m a
    -> Strategy.TransitionT (AppliedRule ReachabilityRule) m a
allPathTransition = Transition.mapRules ruleAllPathToRuleReachability

onePathTransition
    :: Monad m
    => Strategy.TransitionT (AppliedRule OnePathRule) m a
    -> Strategy.TransitionT (AppliedRule ReachabilityRule) m a
onePathTransition = Transition.mapRules ruleOnePathToRuleReachability

maybeOnePath :: ReachabilityRule -> Maybe OnePathRule
maybeOnePath (OnePath rule) = Just rule
maybeOnePath _ = Nothing

maybeAllPath :: ReachabilityRule -> Maybe AllPathRule
maybeAllPath (AllPath rule) = Just rule
maybeAllPath _ = Nothing

ruleAllPathToRuleReachability
    :: AppliedRule AllPathRule
    -> AppliedRule ReachabilityRule
ruleAllPathToRuleReachability (AppliedAxiom (AllPathRewriteRule rewriteRule)) =
    AppliedAxiom (ReachabilityRewriteRule rewriteRule)
ruleAllPathToRuleReachability (AppliedClaim allPathRule) =
    AppliedClaim (AllPath allPathRule)

ruleOnePathToRuleReachability
    :: AppliedRule OnePathRule
    -> AppliedRule ReachabilityRule
ruleOnePathToRuleReachability (AppliedAxiom (OnePathRewriteRule rewriteRule)) =
    AppliedAxiom (ReachabilityRewriteRule rewriteRule)
ruleOnePathToRuleReachability (AppliedClaim onePathRule) =
    AppliedClaim (OnePath onePathRule)

type TransitionRule m rule state =
    Prim -> state -> Strategy.TransitionT rule m state

transitionRule
    :: forall m goal
    .  MonadSimplify m
    => Goal goal
    => [goal]
    -> [[Rule goal]]
    -> TransitionRule m (AppliedRule goal) (ProofState goal)
transitionRule claims axiomGroups = transitionRuleWorker
  where
    transitionRuleWorker
        :: Prim
        -> ProofState goal
        -> Strategy.TransitionT (AppliedRule goal) m (ProofState goal)
    transitionRuleWorker CheckProven Proven = empty
    transitionRuleWorker CheckGoalRemainder (GoalRemainder _) = empty

    transitionRuleWorker ResetGoal (GoalRewritten goal) =
        return (Goal goal)

    transitionRuleWorker CheckGoalStuck (GoalStuck _) = empty

    transitionRuleWorker Simplify (Goal goal) = do
        results <- tryTransitionT (simplify goal)
        case results of
            [] -> return Proven
            _  -> Goal <$> Transition.scatter results

    transitionRuleWorker Simplify (GoalRemainder goal) =
        GoalRemainder <$> simplify goal

    transitionRuleWorker CheckImplication (Goal goal) = do
        result <- checkImplication goal
        case result of
            NotImpliedStuck a -> do
                warnStuckProofStateTermsUnifiable
                pure (GoalStuck a)
            Implied -> pure Proven
            NotImplied a -> pure (Goal a)
    transitionRuleWorker CheckImplication (GoalRemainder goal) = do
        result <- checkImplication goal
        case result of
            NotImpliedStuck a -> do
                warnStuckProofStateTermsUnifiable
                pure (GoalStuck a)
            Implied -> pure Proven
            NotImplied a -> do
                warnStuckProofStateTermsNotUnifiable
                pure (GoalRemainder a)

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
        applyClaims claims goal

    transitionRuleWorker ApplyClaims (GoalRemainder goal) =
        applyClaims claims goal

    transitionRuleWorker ApplyAxioms (Goal goal) =
        applyAxioms axiomGroups goal

    transitionRuleWorker ApplyAxioms (GoalRemainder goal) =
        applyAxioms axiomGroups goal

    transitionRuleWorker _ state = return state

reachabilityFirstStep :: Strategy Prim
reachabilityFirstStep =
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

reachabilityNextStep :: Strategy Prim
reachabilityNextStep =
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

strategy :: Stream (Strategy Prim)
strategy =
    reachabilityFirstStep :> Stream.iterate id reachabilityNextStep

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
    => Lens' goal ClaimPattern
    -> goal
    -> m (CheckImplicationResult goal)
checkImplication' lensRulePattern goal =
    goal
    & Lens.traverseOf lensRulePattern (Compose . checkImplicationWorker)
    & getCompose
  where
    checkImplicationWorker
        :: ClaimPattern
        -> m (CheckImplicationResult ClaimPattern)
    checkImplicationWorker (snd . Step.refreshRule mempty -> claimPattern)
      | isFunctionPattern leftTerm =
        do
            unificationResults <-
                OrPattern.observeAllT unificationProblems
            when
                (all isBottom unificationResults)
                (succeed . NotImplied $ claimPattern)
            removals <-
                OrPattern.observeAllT (removedDestinations unificationResults)
            -- TODO: double check this
            when (all isBottom removals) (succeed Implied)
            simplifiedRemovals <- simplifyConjunctionOfRemovals removals
            when (isBottom simplifiedRemovals) (succeed Implied)
            let stuckConfiguration = OrPattern.toPattern simplifiedRemovals
            claimPattern
                & Lens.set (field @"left") stuckConfiguration
                & NotImpliedStuck
                & pure
        & run
      | otherwise =
      error . show . Pretty.vsep $
          [ "The check implication step expects\
          \ the configuration term to be function-like."
          , Pretty.indent 2 "Configuration term:"
          , Pretty.indent 4 (unparse leftTerm)
          ]
      where
        ClaimPattern { right, left, existentials } = claimPattern
        leftFreeVars = ClaimPattern.freeVariablesLeft claimPattern
        right' =
            ClaimPattern.topExistsToImplicitForall leftFreeVars existentials
            <$> right
        leftTerm = Pattern.term left
        leftCondition = Pattern.withoutTerm left
        leftSort = termLikeSort leftTerm
        sideCondition =
            SideCondition.assumeTrueCondition
                (Condition.fromPredicate . Condition.toPredicate $ leftCondition)

        unificationProblems
            :: LogicT
                (ExceptT (CheckImplicationResult ClaimPattern) m)
                (OrPattern RewritingVariableName)
        unificationProblems = do
            rightPatt <- Logic.scatter right'
            let rightTerm = Pattern.term rightPatt
            mkIn leftSort leftTerm rightTerm
                & Pattern.fromTermLike
                & Pattern.simplify sideCondition

        removedDestinations
            :: MultiOr (OrPattern RewritingVariableName)
            -> LogicT
                (ExceptT (CheckImplicationResult ClaimPattern) m)
                (OrPattern RewritingVariableName)
        removedDestinations unificationResults = do
            singleUnificationCondition <-
                Logic.scatter
                    $ (fmap . fmap) Conditional.withoutTerm unificationResults
            rightCondition <-
                Logic.scatter (Conditional.withoutTerm <$> right')
            simplifiedRightCondition <-
                Condition.simplifyCondition sideCondition rightCondition
                & OrCondition.observeAllT
            remainderConditions <-
                simplifyEvaluatedMultiPredicate
                    sideCondition
                    (MultiAnd.make
                        [ singleUnificationCondition
                        , simplifiedRightCondition
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

        simplifyConjunctionOfRemovals
            :: MultiOr (OrPattern RewritingVariableName)
            -> ExceptT
                (CheckImplicationResult ClaimPattern)
                m
                (OrPattern RewritingVariableName)
        simplifyConjunctionOfRemovals removal = do
            let removalDisjunction =
                    fmap (MultiAnd.toPattern . MultiAnd.make)
                    . MultiOr.fullCrossProduct
                    . MultiOr.extractPatterns
                    $ removal
                definedConfig =
                    Pattern.andCondition left
                    $ from $ makeCeilPredicate_ (Conditional.term left)
                configAndRemoval = fmap (definedConfig <*) removalDisjunction
            simplifyConditionsWithSmt
                sideCondition
                configAndRemoval

        succeed :: r -> ExceptT r m a
        succeed = throwE

        run :: ExceptT r m r -> m r
        run acts = runExceptT acts >>= either pure pure

-- TODO(Ana): simplify right hand side as well
simplify'
    :: MonadSimplify m
    => Lens' goal ClaimPattern
    -> goal
    -> Strategy.TransitionT (AppliedRule goal) m goal
simplify' lensClaimPattern =
    Lens.traverseOf (lensClaimPattern . field @"left") $ \config -> do
        let definedConfig =
                Pattern.andCondition (mkDefined <$> config)
                $ from $ makeCeilPredicate_ (Conditional.term config)
        configs <-
            simplifyTopConfiguration definedConfig
            >>= SMT.Evaluator.filterMultiOr
            & lift
        Foldable.asum (pure <$> configs)

isTriviallyValid' :: Lens' goal ClaimPattern -> goal -> Bool
isTriviallyValid' lensClaimPattern =
    isBottom . Lens.view (lensClaimPattern . field @"left")

isTrusted :: From goal Attribute.Axiom.Trusted => goal -> Bool
isTrusted = Attribute.Trusted.isTrusted . from @_ @Attribute.Axiom.Trusted

-- | Exception that contains the last configuration before the error.
data WithConfiguration =
    WithConfiguration (Pattern VariableName) SomeException
    deriving (Show, Typeable)

instance Exception WithConfiguration

-- | Apply 'Rule's to the goal in parallel.
derivePar'
    :: forall m goal
    .  MonadSimplify m
    => Lens' goal ClaimPattern
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (AppliedRule goal) m (ProofState goal)
derivePar' lensRulePattern mkRule =
    deriveWith lensRulePattern mkRule
    $ Step.applyRewriteRulesParallel Unification.unificationProcedure

type Deriver monad =
        [RewriteRule RewritingVariableName]
    ->  Pattern RewritingVariableName
    ->  monad (Step.Results (RulePattern RewritingVariableName))

-- | Apply 'Rule's to the goal in parallel.
deriveWith
    :: forall m goal
    .  Monad m
    => Lens' goal ClaimPattern
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> Deriver m
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (AppliedRule goal) m (ProofState goal)
deriveWith lensClaimPattern mkRule takeStep rewrites goal =
    getCompose
    $ Lens.forOf lensClaimPattern goal
    $ \claimPattern ->
        fmap (snd . Step.refreshRule mempty)
        $ Lens.forOf (field @"left") claimPattern
        $ \config -> Compose $ do
            results <- takeStep rewrites config & lift
            deriveResults fromAppliedRule results
  where
    fromAppliedRule =
        AppliedAxiom
        . mkRule
        . RewriteRule
        . Step.withoutUnification

-- | Apply 'Rule's to the goal in sequence.
deriveSeq'
    :: forall m goal
    .  MonadSimplify m
    => Lens' goal ClaimPattern
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (AppliedRule goal) m (ProofState goal)
deriveSeq' lensRulePattern mkRule =
    deriveWith lensRulePattern mkRule . flip
    $ Step.applyRewriteRulesSequence Unification.unificationProcedure

deriveResults
    :: Step.UnifyingRuleVariable representation ~ RewritingVariableName
    => (Step.UnifiedRule representation -> AppliedRule goal)
    -> Step.Results representation
    -> Strategy.TransitionT (AppliedRule goal) simplifier
        (ProofState.ProofState (Pattern RewritingVariableName))
-- TODO (thomas.tuegel): Remove goal argument.
deriveResults fromAppliedRule Results { results, remainders } =
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
