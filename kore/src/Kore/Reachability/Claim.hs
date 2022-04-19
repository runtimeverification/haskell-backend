{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Reachability.Claim (
    Claim (..),
    ApplyResult (..),
    AppliedRule (..),
    retractApplyRemainder,
    strategy,
    TransitionRule,
    Prim,
    ClaimExtractor (..),
    WithConfiguration (..),
    CheckImplicationResult (..),
    extractClaims,
    reachabilityFirstStep,
    reachabilityNextStep,
    reachabilityCheckOnly,
    transitionRule,
    isTrusted,

    -- * Re-exports
    RewriteRule (..),
    module Kore.Log.InfoReachability,

    -- * For Claim implementations
    deriveSeqClaim,
    checkImplication',
    simplify',
    derivePar',
    deriveSeq',

    -- * For testing
    checkImplicationWorker,
    simplifyRightHandSide,
) where

import Control.Lens (
    Lens',
 )
import Control.Lens qualified as Lens
import Control.Monad.Catch (
    Exception (..),
    SomeException (..),
 )
import Control.Monad.State.Strict (
    MonadState,
    StateT,
    runStateT,
 )
import Control.Monad.State.Strict qualified as State
import Data.Functor.Compose
import Data.Generics.Product (
    field,
 )
import Data.Monoid qualified as Monoid
import Data.Stream.Infinite (
    Stream (..),
 )
import Data.Stream.Infinite qualified as Stream
import Debug
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Attribute.Axiom qualified as Attribute.Axiom
import Kore.Attribute.Label qualified as Attribute (
    Label,
 )
import Kore.Attribute.RuleIndex qualified as Attribute (
    RuleIndex,
 )
import Kore.Attribute.SourceLocation qualified as Attribute (
    SourceLocation,
 )
import Kore.Attribute.Trusted qualified as Attribute.Trusted
import Kore.IndexedModule.IndexedModule (
    IndexedModule (indexedModuleClaims),
    VerifiedModule,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
    makeInPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Symbol (
    Symbol,
 )
import Kore.Internal.TermLike (
    Not (..),
    Sort,
    isFunctionPattern,
    termLikeSort,
 )
import Kore.Log.InfoReachability
import Kore.Log.WarnClaimRHSIsBottom
import Kore.Reachability.ClaimState hiding (
    claimState,
 )
import Kore.Reachability.Prim
import Kore.Rewrite.AxiomPattern (
    AxiomPattern (..),
 )
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
 )
import Kore.Rewrite.ClaimPattern qualified as ClaimPattern
import Kore.Rewrite.Result (
    Result (..),
    Results (..),
 )
import Kore.Rewrite.RewriteStep qualified as Step
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.RulePattern (
    RewriteRule (..),
    RulePattern (..),
 )
import Kore.Rewrite.SMT.Evaluator qualified as SMT.Evaluator
import Kore.Rewrite.Step qualified as Step
import Kore.Rewrite.Strategy (
    Strategy,
 )
import Kore.Rewrite.Strategy qualified as Strategy
import Kore.Rewrite.Transition qualified as Transition
import Kore.Simplify.Data (
    MonadSimplify,
 )
import Kore.Simplify.Exists qualified as Exists
import Kore.Simplify.Not qualified as Not
import Kore.Simplify.Pattern (
    simplifyTopConfigurationDefined,
 )
import Kore.Simplify.Pattern qualified as Pattern
import Kore.Syntax.Variable
import Kore.TopBottom (
    TopBottom (..),
 )
import Kore.Unparser (
    Unparse (..),
 )
import Kore.Verified qualified as Verified
import Logic (
    LogicT,
    MonadLogic,
 )
import Logic qualified
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Pretty qualified

class Claim claim where
    -- | @Rule claim@ is the type of rule to take a single step toward @claim@.
    data Rule claim

    checkImplication ::
        MonadSimplify m =>
        claim ->
        LogicT m (CheckImplicationResult claim)

    simplify ::
        MonadSimplify m =>
        claim ->
        Strategy.TransitionT (AppliedRule claim) m claim

    applyClaims ::
        MonadSimplify m =>
        [claim] ->
        claim ->
        Strategy.TransitionT (AppliedRule claim) m (ApplyResult claim)

    applyAxioms ::
        MonadSimplify m =>
        [[Rule claim]] ->
        claim ->
        Strategy.TransitionT (AppliedRule claim) m (ApplyResult claim)

{- | 'ApplyResult' is the result of a rewriting step, like 'applyClaims' or 'applyAxioms'.

    Both 'ApplyRewritten' and 'ApplyRemainder' wrap a newly formed claim.
    Its left hand side is constructed from either the application of rewrite rules,
    or, respectively, from the remainder resulting after this procedure.
-}
data ApplyResult claim
    = ApplyRewritten !claim
    | ApplyRemainder !claim
    deriving stock (Show, Eq)
    deriving stock (Functor)

-- | 'AppliedRule' represents the rule applied during a rewriting step.
data AppliedRule claim
    = AppliedAxiom (Rule claim)
    | AppliedClaim claim
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance (Debug claim, Debug (Rule claim)) => Debug (AppliedRule claim)

instance
    ( Diff claim
    , Debug claim
    , Diff (Rule claim)
    , Debug (Rule claim)
    ) =>
    Diff (AppliedRule claim)

instance
    (From claim Attribute.Label, From (Rule claim) Attribute.Label) =>
    From (AppliedRule claim) Attribute.Label
    where
    from (AppliedAxiom rule) = from rule
    from (AppliedClaim claim) = from claim

instance
    (From claim Attribute.RuleIndex, From (Rule claim) Attribute.RuleIndex) =>
    From (AppliedRule claim) Attribute.RuleIndex
    where
    from (AppliedAxiom rule) = from rule
    from (AppliedClaim claim) = from claim

instance
    ( From claim Attribute.SourceLocation
    , From (Rule claim) Attribute.SourceLocation
    ) =>
    From (AppliedRule claim) Attribute.SourceLocation
    where
    from (AppliedAxiom rule) = from rule
    from (AppliedClaim claim) = from claim

instance (Unparse claim, Unparse (Rule claim)) => Unparse (AppliedRule claim) where
    unparse (AppliedAxiom rule) = unparse rule
    unparse (AppliedClaim claim) = unparse claim

    unparse2 (AppliedAxiom rule) = unparse2 rule
    unparse2 (AppliedClaim claim) = unparse2 claim

type AxiomAttributes = Attribute.Axiom.Axiom Symbol VariableName

class ClaimExtractor claim where
    extractClaim :: (AxiomAttributes, Verified.SentenceClaim) -> Maybe claim

-- | Extracts all One-Path claims from a verified module.
extractClaims ::
    ClaimExtractor claim =>
    -- | 'IndexedModule' containing the definition
    VerifiedModule declAtts ->
    [claim]
extractClaims = mapMaybe extractClaim . indexedModuleClaims

deriveSeqClaim ::
    MonadSimplify m =>
    Step.UnifyingRule claim =>
    Step.UnifyingRuleVariable claim ~ RewritingVariableName =>
    From claim (AxiomPattern RewritingVariableName) =>
    From claim Attribute.SourceLocation =>
    Lens' claim ClaimPattern ->
    (ClaimPattern -> claim) ->
    [claim] ->
    claim ->
    Strategy.TransitionT (AppliedRule claim) m (ApplyResult claim)
deriveSeqClaim lensClaimPattern mkClaim claims claim =
    getCompose $
        Lens.forOf lensClaimPattern claim $
            \claimPattern ->
                fmap (snd . Step.refreshRule mempty) $
                    Lens.forOf (field @"left") claimPattern $
                        \config -> Compose $ do
                            let claimPatSort = ClaimPattern.getClaimPatternSort claimPattern
                            results <-
                                Step.applyClaimsSequence
                                    mkClaim
                                    config
                                    (Lens.view lensClaimPattern <$> claims)
                                    & lift
                            deriveResults claimPatSort fromAppliedRule results
  where
    fromAppliedRule =
        AppliedClaim
            . mkClaim
            . Step.withoutUnification

type TransitionRule m rule state =
    Prim -> state -> Strategy.TransitionT rule m state

transitionRule ::
    forall m claim.
    MonadSimplify m =>
    Claim claim =>
    [claim] ->
    [[Rule claim]] ->
    TransitionRule m (AppliedRule claim) (ClaimState claim)
transitionRule claims axiomGroups = transitionRuleWorker
  where
    transitionRuleWorker ::
        Prim ->
        ClaimState claim ->
        Strategy.TransitionT (AppliedRule claim) m (ClaimState claim)

    transitionRuleWorker Begin Proven = empty
    transitionRuleWorker Begin (Stuck _) = empty
    transitionRuleWorker Begin (Rewritten claim) = pure (Claimed claim)
    transitionRuleWorker Begin claimState = pure claimState
    transitionRuleWorker Simplify claimState
        | Just claim <- retractSimplifiable claimState =
            Transition.ifte (simplify claim) (pure . ($>) claimState) (pure Proven)
        | otherwise =
            pure claimState
    transitionRuleWorker CheckImplication claimState
        | Just claim <- retractRewritable claimState = do
            result <- checkImplication claim & Logic.lowerLogicT
            case result of
                Implied -> pure Proven
                NotImpliedStuck a -> do
                    pure (Stuck a)
                NotImplied a
                    | isRemainder claimState -> do
                        pure (Stuck a)
                    | otherwise -> pure (Claimed a)
        | otherwise = pure claimState
    transitionRuleWorker ApplyClaims (Claimed claim) =
        Transition.ifte
            (applyClaims claims claim)
            (return . applyResultToClaimState)
            (pure Proven)
    transitionRuleWorker ApplyClaims claimState = pure claimState
    transitionRuleWorker ApplyAxioms claimState
        | Just claim <- retractRewritable claimState =
            Transition.ifte
                (applyAxioms axiomGroups claim)
                (return . applyResultToClaimState)
                (pure Proven)
        | otherwise = pure claimState

    applyResultToClaimState (ApplyRewritten a) = Rewritten a
    applyResultToClaimState (ApplyRemainder a) = Remaining a

retractSimplifiable :: ClaimState a -> Maybe a
retractSimplifiable (Claimed a) = Just a
retractSimplifiable (Rewritten a) = Just a
retractSimplifiable (Remaining a) = Just a
retractSimplifiable _ = Nothing

retractApplyRemainder :: ApplyResult a -> Maybe a
retractApplyRemainder (ApplyRemainder a) = Just a
retractApplyRemainder _ = Nothing

isRemainder :: ClaimState a -> Bool
isRemainder (Remaining _) = True
isRemainder _ = False

reachabilityFirstStep :: Strategy Prim
reachabilityFirstStep =
    (Strategy.sequence . map Strategy.apply)
        [ Begin
        , Simplify
        , CheckImplication
        , ApplyAxioms
        , Simplify
        ]

reachabilityNextStep :: Strategy Prim
reachabilityNextStep =
    (Strategy.sequence . map Strategy.apply)
        [ Begin
        , Simplify
        , CheckImplication
        , ApplyClaims
        , ApplyAxioms
        , Simplify
        ]

-- | A strategy for the last step of depth-limited reachability proofs.
--   The final such step should only perform a CheckImplication.
reachabilityCheckOnly :: Strategy Prim
reachabilityCheckOnly =
    Strategy.sequence [Strategy.apply Begin, Strategy.apply CheckImplication]

strategy :: Stream (Strategy Prim)
strategy =
    reachabilityFirstStep :> Stream.iterate id reachabilityNextStep

{- | The result of checking the direct implication of a proof claim.

As an optimization, 'checkImplication' returns 'NotImpliedStuck' when the
implication between /terms/ is valid, but the implication between side
conditions does not hold.
-}
data CheckImplicationResult a
    = -- | The implication is valid.
      Implied
    | -- | The implication is not valid.
      NotImplied !a
    | -- | The implication between /terms/ is valid, but the implication between
      -- side-conditions is not valid.
      NotImpliedStuck !a
    deriving stock (Eq, Ord, Show)
    deriving stock (Foldable, Functor, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Pretty a => Pretty (CheckImplicationResult a) where
    pretty Implied = "implied"
    pretty (NotImplied a) =
        Pretty.vsep
            [ "not implied:"
            , Pretty.indent 4 $ pretty a
            ]
    pretty (NotImpliedStuck a) =
        Pretty.vsep
            [ "stuck:"
            , Pretty.indent 4 $ pretty a
            ]

-- | Remove the destination of the claim.
checkImplication' ::
    forall claim m.
    (MonadLogic m, MonadSimplify m) =>
    Lens' claim ClaimPattern ->
    claim ->
    m (CheckImplicationResult claim)
checkImplication' lensRulePattern claim =
    claim
        & Lens.traverseOf lensRulePattern (Compose . checkImplicationWorker)
        & getCompose

assertFunctionLikeConfiguration ::
    forall m.
    Monad m =>
    HasCallStack =>
    ClaimPattern ->
    m ()
assertFunctionLikeConfiguration claimPattern
    | (not . isFunctionPattern) leftTerm =
        error . show . Pretty.vsep $
            [ "The check implication step expects\
              \ the configuration term to be function-like."
            , Pretty.indent 2 "Configuration term:"
            , Pretty.indent 4 (unparse leftTerm)
            ]
    | otherwise = pure ()
  where
    ClaimPattern{left} = claimPattern
    leftTerm = Pattern.term left

newtype AnyUnified = AnyUnified {didAnyUnify :: Bool}
    deriving stock (Eq, Ord, Read, Show)
    deriving (Semigroup, Monoid) via Monoid.Any

{- | Check the claim by direct implication.

The claim has the form

@
φ(X) → ∘ ∃ Y. ⋁ᵢ ψᵢ(X, Y)
@

where @∘ _@ is a modality in reachability logic. @φ@ and the @ψᵢ@ are assumed to
be function-like patterns. @X@ and @Y@ are disjoint families of
variables. @checkImplicationWorker@ checks the validity of the formula

@
⌊ φ(X) → ∃ Y. ⋁ᵢ ψᵢ(X, Y) ⌋
@

Let @φ(X) = t(X) ∧ P(X)@ and @ψᵢ(X, Y) = tᵢ(X, Y) ∧ Pᵢ(X, Y)@; then the
implication formula above is valid when

@
(⋀ᵢ ¬ ∃ Y. ⌈t(X) ∧ tᵢ(X, Y)⌉ ∧ Pᵢ(X, Y)) ∧ ⌈t(X)⌉ ∧ P(X)
@

is unsatisfiable. This predicate basically consists of two parts: a single positive
conjunct asserting that the left-hand side of the claim is satisfiable:

@
⌈t(X)⌉ ∧ P(X)
@

and many negative conjuncts arising from the unification of the left- and
right-hand sides:

@
⋀ᵢ ¬ ∃ Y. ⌈t(X) ∧ tᵢ(X, Y)⌉ ∧ Pᵢ(X, Y)
@

When the implication formula is valid, @checkImplicationWorker@ returns
'Implied'. When the implication formula is not valid, we apply the following
heuristic:

* If any of the unification problems @⌈t(X) ∧ tᵢ(X, Y)⌉@ succeeded,
  @checkImplicationWorker@ returns 'NotImpliedStuck',
* otherwise, it returns 'NotImplied'.

Returing 'NotImpliedStuck' has the effect of terminating the proof. This
heuristic prevents the prover from executing beyond the intended final program
state ("inventing" programs), but at the cost that it does prevent the prover
from visiting the final program state twice. In practice, we find that deductive
proofs should not require the prover to visit the final program state twice,
anyway.
-}
checkImplicationWorker ::
    forall m.
    (MonadLogic m, MonadSimplify m) =>
    ClaimPattern ->
    m (CheckImplicationResult ClaimPattern)
checkImplicationWorker (ClaimPattern.refreshExistentials -> claimPattern) =
    do
        (anyUnified, removal) <- getNegativeConjuncts
        let definedConfig =
                Pattern.andCondition left $
                    from $ makeCeilPredicate leftTerm
        let configs' = MultiOr.map (definedConfig <*) removal
        stuck <-
            Logic.scatter configs'
                >>= Pattern.simplify
                >>= SMT.Evaluator.filterMultiOr
                >>= Logic.scatter
        examine anyUnified stuck
        & elseImplied
  where
    ClaimPattern{right, left, existentials} = claimPattern
    leftTerm = Pattern.term left
    sort = termLikeSort leftTerm
    leftCondition = Pattern.withoutTerm left

    -- TODO (#1278): Do not combine the predicate and the substitution.
    -- This is held over from the old representation of claims, which did not
    -- distinguish the predicate and substitution in the first place. We can't
    -- use the substitution directly yet, because it isn't kept normalized. Once
    -- the claim is fully simplified at every step, that should not be a
    -- problem.
    sideCondition =
        SideCondition.fromConditionWithReplacements
            ( Condition.fromPredicate
                . Condition.toPredicate
                $ leftCondition
            )

    getNegativeConjuncts :: m (AnyUnified, OrPattern RewritingVariableName)
    getNegativeConjuncts =
        do
            assertFunctionLikeConfiguration claimPattern
            right' <- Logic.scatter right
            let (rightTerm, rightCondition) = Pattern.splitTerm right'
            unified <-
                makeInPredicate leftTerm rightTerm
                    & Pattern.fromPredicateSorted sort
                    & Pattern.simplify
                    & (>>= Logic.scatter)
            didUnify
            removed <-
                Pattern.andCondition unified rightCondition
                    & Pattern.simplify
                    & (>>= Logic.scatter)
            Exists.makeEvaluate sideCondition existentials removed
                >>= Logic.scatter
            & OrPattern.observeAllT
            & (>>= mkNotSimplified)
            & wereAnyUnified
      where
        mkNotSimplified notChild =
            Not.simplify sideCondition Not{notSort = sort, notChild}

    wereAnyUnified :: StateT AnyUnified m a -> m (AnyUnified, a)
    wereAnyUnified act = swap <$> runStateT act mempty

    didUnify :: MonadState AnyUnified state => state ()
    didUnify = State.put (AnyUnified True)

    elseImplied acts = Logic.ifte acts pure (pure Implied)

    examine ::
        AnyUnified ->
        Pattern RewritingVariableName ->
        m (CheckImplicationResult ClaimPattern)
    examine AnyUnified{didAnyUnify} stuck
        | didAnyUnify
          , isBottom condition =
            pure Implied
        | not didAnyUnify
          , not (isBottom right) =
            pure $ NotImplied claimPattern
        | otherwise = do
            when (isBottom right) $
                warnClaimRHSIsBottom claimPattern
            pure $
                Lens.set (field @"left") stuck claimPattern
                    & NotImpliedStuck
      where
        (_, condition) = Pattern.splitTerm stuck

simplify' ::
    MonadSimplify m =>
    Lens' claim ClaimPattern ->
    claim ->
    Strategy.TransitionT (AppliedRule claim) m claim
simplify' lensClaimPattern claim = do
    claim' <- simplifyLeftHandSide claim
    let claim'' = Lens.over lensClaimPattern applySubstOnRightHandSide claim'
        sideCondition = extractSideCondition claim''
    simplifyRightHandSide lensClaimPattern sideCondition claim''
  where
    applySubstOnRightHandSide :: ClaimPattern -> ClaimPattern
    applySubstOnRightHandSide claimPat@ClaimPattern{left, right} =
        let substitution = Pattern.substitution left
            mapSubstitution ::
                Pattern RewritingVariableName -> Pattern RewritingVariableName
            mapSubstitution = Lens.over (field @"substitution") (substitution <>)
            right' = MultiOr.map mapSubstitution right
         in claimPat{right = right'}
    extractSideCondition =
        SideCondition.fromConditionWithReplacements
            . Pattern.withoutTerm
            . Lens.view (lensClaimPattern . field @"left")

    simplifyLeftHandSide =
        Lens.traverseOf (lensClaimPattern . field @"left") $ \config -> do
            configs <-
                simplifyTopConfigurationDefined
                    config
                    >>= SMT.Evaluator.filterMultiOr
                    & lift
            asum (pure <$> toList configs)

simplifyRightHandSide ::
    MonadSimplify m =>
    Lens' claim ClaimPattern ->
    SideCondition RewritingVariableName ->
    claim ->
    m claim
simplifyRightHandSide lensClaimPattern sideCondition =
    Lens.traverseOf (lensClaimPattern . field @"right") $ \dest ->
        OrPattern.observeAllT $
            Logic.scatter dest
                >>= Pattern.makeEvaluate sideCondition . Pattern.requireDefined
                >>= SMT.Evaluator.filterMultiOr
                >>= Logic.scatter

isTrusted :: From claim Attribute.Axiom.Trusted => claim -> Bool
isTrusted = Attribute.Trusted.isTrusted . from @_ @Attribute.Axiom.Trusted

-- | Exception that contains the last configuration before the error.
data WithConfiguration
    = WithConfiguration (Pattern VariableName) SomeException
    deriving stock (Show, Typeable)

instance Exception WithConfiguration

-- | Apply 'Rule's to the claim in parallel.
derivePar' ::
    forall m claim.
    MonadSimplify m =>
    Lens' claim ClaimPattern ->
    (RewriteRule RewritingVariableName -> Rule claim) ->
    [RewriteRule RewritingVariableName] ->
    claim ->
    Strategy.TransitionT (AppliedRule claim) m (ApplyResult claim)
derivePar' lensRulePattern mkRule =
    deriveWith lensRulePattern mkRule Step.applyRewriteRulesParallel

type Deriver monad =
    [RewriteRule RewritingVariableName] ->
    Pattern RewritingVariableName ->
    monad (Step.Results (RulePattern RewritingVariableName))

-- | Apply 'Rule's to the claim in parallel.
deriveWith ::
    forall m claim.
    Monad m =>
    Lens' claim ClaimPattern ->
    (RewriteRule RewritingVariableName -> Rule claim) ->
    Deriver m ->
    [RewriteRule RewritingVariableName] ->
    claim ->
    Strategy.TransitionT (AppliedRule claim) m (ApplyResult claim)
deriveWith lensClaimPattern mkRule takeStep rewrites claim =
    getCompose $
        Lens.forOf lensClaimPattern claim $
            \claimPattern ->
                fmap (snd . Step.refreshRule mempty) $
                    Lens.forOf (field @"left") claimPattern $
                        \config -> Compose $ do
                            let claimPatSort = ClaimPattern.getClaimPatternSort claimPattern
                            results <- takeStep rewrites config & lift
                            deriveResults claimPatSort fromAppliedRule results
  where
    fromAppliedRule =
        AppliedAxiom
            . mkRule
            . RewriteRule
            . Step.withoutUnification

-- | Apply 'Rule's to the claim in sequence.
deriveSeq' ::
    forall m claim.
    MonadSimplify m =>
    Lens' claim ClaimPattern ->
    (RewriteRule RewritingVariableName -> Rule claim) ->
    [RewriteRule RewritingVariableName] ->
    claim ->
    Strategy.TransitionT (AppliedRule claim) m (ApplyResult claim)
deriveSeq' lensRulePattern mkRule =
    deriveWith lensRulePattern mkRule $ flip Step.applyRewriteRulesSequence

deriveResults ::
    Step.UnifyingRuleVariable representation ~ RewritingVariableName =>
    Sort ->
    (Step.UnifiedRule representation -> AppliedRule claim) ->
    Step.Results representation ->
    Strategy.TransitionT
        (AppliedRule claim)
        simplifier
        (ApplyResult (Pattern RewritingVariableName))
-- TODO (thomas.tuegel): Remove claim argument.
deriveResults sort fromAppliedRule Results{results, remainders} =
    addResults <|> addRemainders
  where
    addResults = asum (addResult <$> results)
    addRemainders = asum (addRemainder <$> toList remainders)

    addResult Result{appliedRule, result} = do
        addRule appliedRule
        case toList result of
            [] -> addRewritten (Pattern.bottomOf sort)
            configs -> asum (addRewritten <$> configs)

    addRewritten = pure . ApplyRewritten
    addRemainder = pure . ApplyRemainder

    addRule = Transition.addRule . fromAppliedRule
