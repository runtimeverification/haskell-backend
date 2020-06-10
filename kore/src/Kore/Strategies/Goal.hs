{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.Goal
    ( Goal (..)
    , FromRulePattern (..)
    , ClaimExtractor (..)
    , TransitionRuleTemplate (..)
    , WithConfiguration (..)
    , extractClaims
    , unprovenNodes
    , proven
    , onePathFirstStep
    , onePathFollowupStep
    , allPathFirstStep
    , allPathFollowupStep
    , getConfiguration
    , getDestination
    , transitionRuleTemplate
    , isTrusted
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
import Control.Exception
    ( throw
    )
import Control.Lens
    ( Lens'
    )
import qualified Control.Lens as Lens
import Control.Monad.Catch
    ( Exception (..)
    , MonadCatch
    , SomeException (..)
    , handle
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
import Data.Kind
    ( Type
    )
import Data.List.Extra
    ( groupSortOn
    , sortOn
    )
import qualified Data.Set as Set
import Data.Stream.Infinite
    ( Stream (..)
    )
import qualified Data.Stream.Infinite as Stream

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import Kore.Attribute.Pattern.FreeVariables
    ( freeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import qualified Kore.Attribute.Trusted as Attribute.Trusted
import Kore.IndexedModule.IndexedModule
    ( IndexedModule (indexedModuleClaims)
    , VerifiedModule
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
    ( assumeTrueCondition
    )
import Kore.Internal.Symbol
    ( Symbol
    )
import Kore.Internal.TermLike
    ( isElementVariable
    , isFunctionPattern
    , mkAnd
    , retractElementVariable
    )
import Kore.Log.DebugProofState
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
import Kore.Step.Simplification.Data
    ( InternalVariable
    , MonadSimplify
    )
import qualified Kore.Step.Simplification.Exists as Exists
import Kore.Step.Simplification.Pattern
    ( simplifyTopConfiguration
    )
import Kore.Step.Simplification.Simplify
    ( simplifyConditionalTermToOr
    )
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
    ( Prim
    , ProofState
    , proofState
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
import Log
    ( MonadLog (..)
    )
import qualified Pretty

{- | The final nodes of an execution graph which were not proven.

See also: 'Strategy.pickFinal', 'extractUnproven'

 -}
unprovenNodes
    :: forall goal a
    .  ProofState.ProofState a ~ ProofState goal a
    => Strategy.ExecutionGraph (ProofState goal a) (Rule goal)
    -> MultiOr.MultiOr a
unprovenNodes executionGraph =
    MultiOr.MultiOr
    $ mapMaybe extractUnproven
    $ Strategy.pickFinal executionGraph

{- | Does the 'Strategy.ExecutionGraph' indicate a successful proof?
 -}
proven
    :: forall goal a
    .  ProofState.ProofState a ~ ProofState goal a
    => Strategy.ExecutionGraph (ProofState goal a) (Rule goal)
    -> Bool
proven = Foldable.null . unprovenNodes

class Goal goal where
    type Prim goal
    type ProofState goal :: Type -> Type

    goalToRule :: goal -> Rule goal
    default goalToRule
        :: Coercible goal (Rule goal)
        => goal -> Rule goal
    goalToRule = coerce

    transitionRule
        :: (MonadCatch m, MonadSimplify m)
        => Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)

    strategy
        :: goal
        -> [goal]
        -> [Rule goal]
        -> Stream (Strategy (Prim goal))

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
    type Prim OnePathRule = ProofState.Prim (Rule OnePathRule)
    type ProofState OnePathRule = ProofState.ProofState

    goalToRule =
        OnePathRewriteRule
        . mkRewritingRule
        . RewriteRule
        . getOnePathRule

    transitionRule =
        (withDebugProofState . transitionRuleTemplate)
        TransitionRuleTemplate
            { simplifyTemplate = simplify _Unwrapped
            , removeDestinationTemplate = removeDestination _Unwrapped
            , isTriviallyValidTemplate = isTriviallyValid _Unwrapped
            , deriveParTemplate = deriveParOnePath
            , deriveSeqTemplate = deriveSeqOnePath
            }

    strategy _ goals rules =
        onePathFirstStep rewrites
        :> Stream.iterate
            id
            ( onePathFollowupStep
                coinductiveRewrites
                rewrites
            )
      where
        rewrites = sortOn Attribute.Axiom.getPriorityOfAxiom rules
        coinductiveRewrites = goalToRule <$> goals

deriveParOnePath
    ::  (MonadCatch simplifier, MonadSimplify simplifier)
    =>  [Rule OnePathRule]
    ->  OnePathRule
    ->  Strategy.TransitionT (Rule OnePathRule) simplifier
            (ProofState OnePathRule OnePathRule)
deriveParOnePath rules =
    derivePar _Unwrapped OnePathRewriteRule rewrites
  where
    rewrites = unRuleOnePath <$> rules

deriveSeqOnePath
    ::  (MonadCatch simplifier, MonadSimplify simplifier)
    =>  [Rule OnePathRule]
    ->  OnePathRule
    ->  Strategy.TransitionT (Rule OnePathRule) simplifier
            (ProofState OnePathRule OnePathRule)
deriveSeqOnePath rules =
    deriveSeq _Unwrapped OnePathRewriteRule rewrites
  where
    rewrites = unRuleOnePath <$> rules

instance ClaimExtractor OnePathRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (OnePathClaimPattern claim) -> Just claim
            _ -> Nothing

instance Goal AllPathRule where
    type Prim AllPathRule = ProofState.Prim (Rule AllPathRule)
    type ProofState AllPathRule = ProofState.ProofState

    goalToRule =
        AllPathRewriteRule
        . mkRewritingRule
        . RewriteRule
        . getAllPathRule

    transitionRule =
        (withDebugProofState . transitionRuleTemplate)
        TransitionRuleTemplate
            { simplifyTemplate = simplify _Unwrapped
            , removeDestinationTemplate = removeDestination _Unwrapped
            , isTriviallyValidTemplate = isTriviallyValid _Unwrapped
            , deriveParTemplate = deriveParAllPath
            , deriveSeqTemplate = deriveSeqAllPath
            }

    strategy _ goals rules =
        allPathFirstStep priorityGroups
        :> Stream.iterate
            id
            ( allPathFollowupStep
                coinductiveRewrites
                priorityGroups
            )
      where
        priorityGroups = groupSortOn Attribute.Axiom.getPriorityOfAxiom rules
        coinductiveRewrites = goalToRule <$> goals

deriveParAllPath
    ::  (MonadCatch simplifier, MonadSimplify simplifier)
    =>  [Rule AllPathRule]
    ->  AllPathRule
    ->  Strategy.TransitionT (Rule AllPathRule) simplifier
            (ProofState AllPathRule AllPathRule)
deriveParAllPath rules =
    derivePar _Unwrapped AllPathRewriteRule rewrites
  where
    rewrites = unRuleAllPath <$> rules

deriveSeqAllPath
    ::  (MonadCatch simplifier, MonadSimplify simplifier)
    =>  [Rule AllPathRule]
    ->  AllPathRule
    ->  Strategy.TransitionT (Rule AllPathRule) simplifier
            (ProofState AllPathRule AllPathRule)
deriveSeqAllPath rules =
    deriveSeq _Unwrapped AllPathRewriteRule rewrites
  where
    rewrites = unRuleAllPath <$> rules

instance ClaimExtractor AllPathRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (AllPathClaimPattern claim) -> Just claim
            _ -> Nothing

instance Goal ReachabilityRule where
    type Prim ReachabilityRule = ProofState.Prim (Rule ReachabilityRule)
    type ProofState ReachabilityRule = ProofState.ProofState

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

    transitionRule
        :: (MonadCatch m, MonadSimplify m)
        => Prim ReachabilityRule
        -> ProofState
            ReachabilityRule
            ReachabilityRule
        -> Strategy.TransitionT
            (Rule ReachabilityRule)
            m
            ( ProofState
                ReachabilityRule
                ReachabilityRule
            )
    transitionRule = logTransitionRule $ \prim proofstate ->
        case proofstate of
            Goal (OnePath rule) ->
                Transition.mapRules ruleOnePathToRuleReachability
                $ onePathProofState
                <$> transitionRule (primRuleOnePath prim) (Goal rule)
            Goal (AllPath rule) ->
                Transition.mapRules ruleAllPathToRuleReachability
                $ allPathProofState
                <$> transitionRule (primRuleAllPath prim) (Goal rule)
            GoalRewritten (OnePath rule) ->
                Transition.mapRules ruleOnePathToRuleReachability
                $ onePathProofState
                <$> transitionRule (primRuleOnePath prim) (GoalRewritten rule)
            GoalRewritten (AllPath rule) ->
                Transition.mapRules ruleAllPathToRuleReachability
                $ allPathProofState
                <$> transitionRule (primRuleAllPath prim) (GoalRewritten rule)
            GoalRemainder (OnePath rule) ->
                Transition.mapRules ruleOnePathToRuleReachability
                $ onePathProofState
                <$> transitionRule (primRuleOnePath prim) (GoalRemainder rule)
            GoalRemainder (AllPath rule) ->
                Transition.mapRules ruleAllPathToRuleReachability
                $ allPathProofState
                <$> transitionRule (primRuleAllPath prim) (GoalRemainder rule)
            state@(GoalStuck _) ->
                case prim of
                    CheckGoalStuck -> debugProofStateFinal state CheckGoalStuck
                    _ -> return proofstate
            Proven ->
                case prim of
                    CheckProven -> debugProofStateFinal Proven CheckProven
                    _ -> return proofstate

    strategy
        :: ReachabilityRule
        -> [ReachabilityRule]
        -> [Rule ReachabilityRule]
        -> Stream (Strategy (Prim ReachabilityRule))
    strategy goal claims axioms =
        case goal of
            OnePath rule ->
                reachabilityOnePathStrategy
                $ strategy
                    rule
                    (mapMaybe maybeOnePath claims)
                    (fmap ruleReachabilityToRuleOnePath axioms)
            AllPath rule ->
                reachabilityAllPathStrategy
                $ strategy
                    rule
                    (mapMaybe maybeAllPath claims)
                    (fmap ruleReachabilityToRuleAllPath axioms)

instance ClaimExtractor ReachabilityRule where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (OnePathClaimPattern claim) -> Just (OnePath claim)
            Right (AllPathClaimPattern claim) -> Just (AllPath claim)
            _ -> Nothing

maybeOnePath :: ReachabilityRule -> Maybe OnePathRule
maybeOnePath (OnePath rule) = Just rule
maybeOnePath _ = Nothing

maybeAllPath :: ReachabilityRule -> Maybe AllPathRule
maybeAllPath (AllPath rule) = Just rule
maybeAllPath _ = Nothing

reachabilityOnePathStrategy
    :: Functor t
    => t (Strategy (Prim OnePathRule))
    -> t (Strategy (Prim ReachabilityRule))
reachabilityOnePathStrategy strategy' =
    (fmap . fmap . fmap)
        ruleOnePathToRuleReachability
        strategy'

reachabilityAllPathStrategy
    :: Functor t
    => t (Strategy (Prim AllPathRule))
    -> t (Strategy (Prim ReachabilityRule))
reachabilityAllPathStrategy strategy' =
    (fmap . fmap . fmap)
        ruleAllPathToRuleReachability
        strategy'

allPathProofState
    :: ProofState AllPathRule AllPathRule
    -> ProofState ReachabilityRule ReachabilityRule
allPathProofState = fmap AllPath

onePathProofState
    :: ProofState OnePathRule OnePathRule
    -> ProofState ReachabilityRule ReachabilityRule
onePathProofState = fmap OnePath

primRuleOnePath
    :: ProofState.Prim (Rule ReachabilityRule)
    -> ProofState.Prim (Rule OnePathRule)
primRuleOnePath = fmap ruleReachabilityToRuleOnePath

primRuleAllPath
    :: ProofState.Prim (Rule ReachabilityRule)
    -> ProofState.Prim (Rule AllPathRule)
primRuleAllPath = fmap ruleReachabilityToRuleAllPath

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

data TransitionRuleTemplate monad goal =
    TransitionRuleTemplate
    { simplifyTemplate
        :: goal -> Strategy.TransitionT (Rule goal) monad goal
    , removeDestinationTemplate
        :: (forall x. x -> ProofState goal x)
        -> goal
        -> Strategy.TransitionT (Rule goal) monad (ProofState goal goal)
    , isTriviallyValidTemplate :: goal -> Bool
    , deriveParTemplate
        :: [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) monad (ProofState goal goal)
    , deriveSeqTemplate
        :: [Rule goal]
        -> goal
        -> Strategy.TransitionT (Rule goal) monad (ProofState goal goal)
    }

logTransitionRule
    :: forall m goal
    .  MonadSimplify m
    => goal ~ ReachabilityRule
    =>  (  Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
        )
    ->  (  Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
        )
logTransitionRule rule prim proofState = case proofState of
    Goal goal          -> logWith goal
    GoalRemainder goal -> logWith goal
    _                  -> rule prim proofState
  where
    logWith goal = case prim of
        Simplify ->
            whileSimplify goal $ rule prim proofState
        RemoveDestination ->
            whileRemoveDestination goal $ rule prim proofState
        (DeriveSeq rules) ->
            whileDeriveSeq rules goal $ rule prim proofState
        (DerivePar rules) ->
            whileDerivePar rules goal $ rule prim proofState
        _ ->
            rule prim proofState

transitionRuleTemplate
    :: forall m goal
    .  MonadSimplify m
    => ProofState goal goal ~ ProofState.ProofState goal
    => Prim goal ~ ProofState.Prim (Rule goal)
    => TransitionRuleTemplate m goal
    -> Prim goal
    -> ProofState goal goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
transitionRuleTemplate
    TransitionRuleTemplate
        { simplifyTemplate
        , removeDestinationTemplate
        , isTriviallyValidTemplate
        , deriveParTemplate
        , deriveSeqTemplate
        }
  =
    transitionRuleWorker
  where
    transitionRuleWorker
        :: Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
    transitionRuleWorker CheckProven Proven = empty
    transitionRuleWorker CheckGoalRemainder (GoalRemainder _) = empty

    transitionRuleWorker ResetGoal (GoalRewritten goal) =
        return (Goal goal)

    transitionRuleWorker CheckGoalStuck (GoalStuck _) = empty

    transitionRuleWorker Simplify (Goal goal) =
        Profile.timeStrategy "Goal.Simplify" $ do
            results <- tryTransitionT (simplifyTemplate goal)
            case results of
                [] -> return Proven
                _  -> Goal <$> Transition.scatter results

    transitionRuleWorker Simplify (GoalRemainder goal) =
        Profile.timeStrategy "Goal.SimplifyRemainder"
        $ GoalRemainder <$> simplifyTemplate goal

    transitionRuleWorker RemoveDestination (Goal goal) =
        Profile.timeStrategy "Goal.RemoveDestination"
        $ removeDestinationTemplate Goal goal
    transitionRuleWorker RemoveDestination (GoalRemainder goal) =
        Profile.timeStrategy "Goal.RemoveDestinationRemainder"
        $ removeDestinationTemplate GoalRemainder goal

    transitionRuleWorker TriviallyValid (Goal goal)
      | isTriviallyValidTemplate goal =
          return Proven
    transitionRuleWorker TriviallyValid (GoalRemainder goal)
      | isTriviallyValidTemplate goal =
          return Proven
    transitionRuleWorker TriviallyValid (GoalRewritten goal)
      | isTriviallyValidTemplate goal =
          return Proven

    transitionRuleWorker (DerivePar rules) (Goal goal) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        --
        -- Note that in most transitions it is obvious what is being transformed
        -- into what, e.g. that a `ResetGoal` transition transforms
        -- `GoalRewritten` into `Goal`. However, here we're taking a `Goal`
        -- and transforming it into `GoalRewritten` and `GoalRemainder` in an
        -- opaque way. I think that there's no good reason for wrapping the
        -- results in `derivePar` as opposed to here.
        Profile.timeStrategy "Goal.DerivePar"
        $ deriveParTemplate rules goal
    transitionRuleWorker (DerivePar rules) (GoalRemainder goal) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        -- See above for an explanation.
        Profile.timeStrategy "Goal.DeriveParRemainder"
        $ deriveParTemplate rules goal

    transitionRuleWorker (DeriveSeq rules) (Goal goal) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        -- See above for an explanation.
        Profile.timeStrategy "Goal.DeriveSeq"
        $ deriveSeqTemplate rules goal
    transitionRuleWorker (DeriveSeq rules) (GoalRemainder goal) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        -- See above for an explanation.
        Profile.timeStrategy "Goal.DeriveSeqRemainder"
        $ deriveSeqTemplate rules goal

    transitionRuleWorker _ state = return state

onePathFirstStep
    :: Prim goal ~ ProofState.Prim (Rule goal)
    => [Rule goal]
    -> Strategy (Prim goal)
onePathFirstStep axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalStuck
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , DeriveSeq axioms
        , Simplify
        , TriviallyValid
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

onePathFollowupStep
    :: Prim goal ~ ProofState.Prim (Rule goal)
    => [Rule goal]
    -> [Rule goal]
    -> Strategy (Prim goal)
onePathFollowupStep claims axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalStuck
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , DeriveSeq claims
        , Simplify
        , TriviallyValid
        , DeriveSeq axioms
        , Simplify
        , TriviallyValid
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

groupStrategy
    :: [[Rule AllPathRule]]
    -> [Prim AllPathRule]
groupStrategy [] =
    [DerivePar [], Simplify, TriviallyValid]
groupStrategy axiomGroups = do
    group <- axiomGroups
    [DerivePar group, Simplify, TriviallyValid]

allPathFirstStep
    :: [[Rule AllPathRule]]
    -> Strategy (Prim AllPathRule)
allPathFirstStep axiomGroups =
    (Strategy.sequence . map Strategy.apply) $
        [ CheckProven
        , CheckGoalStuck
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        ]
        <> groupStrategy axiomGroups <>
        [ ResetGoal
        , Simplify
        , TriviallyValid
        ]

allPathFollowupStep
    :: [Rule AllPathRule]
    -> [[Rule AllPathRule]]
    -> Strategy (Prim AllPathRule)
allPathFollowupStep claims axiomGroups =
    (Strategy.sequence . map Strategy.apply) $
        [ CheckProven
        , CheckGoalStuck
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , DeriveSeq claims
        , Simplify
        , TriviallyValid
        ]
        <> groupStrategy axiomGroups <>
        [ ResetGoal
        , Simplify
        , TriviallyValid
        ]

-- | Remove the destination of the goal.
removeDestination
    :: forall goal m
    .  MonadSimplify m
    => MonadCatch m
    => ProofState.ProofState goal ~ ProofState goal goal
    => Lens' goal (RulePattern VariableName)
    -> (forall x. x -> ProofState goal x)
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
removeDestination lensRulePattern mkState goal =
    goal
    & Lens.traverseOf lensRulePattern (Compose . removeDestinationWorker)
    & getCompose
    & lift
  where
    removeDestinationWorker
        :: RulePattern VariableName
        -> m (ProofState goal (RulePattern VariableName))
    removeDestinationWorker rulePattern =
        do
            removal <- removalPredicate destination configuration
            when (isTop removal) (succeed . mkState $ rulePattern)
            simplifiedRemoval <-
                return (Conditional.andPredicate configuration removal)
                >>= simplifyTopConfiguration
                >>= SMT.Evaluator.filterMultiOr
            when (isBottom simplifiedRemoval) (succeed Proven)
            let stuckConfiguration = OrPattern.toPattern simplifiedRemoval
            rulePattern
                & Lens.set RulePattern.leftPattern stuckConfiguration
                & GoalStuck
                & pure
        & run
        & withConfiguration configuration
      where
        configuration = Lens.view RulePattern.leftPattern rulePattern
        configFreeVars = freeVariables configuration
        destination =
            Lens.view (field @"rhs") rulePattern
            & topExistsToImplicitForall configFreeVars

        succeed :: r -> ExceptT r m a
        succeed = throwE

        run :: ExceptT r m r -> m r
        run acts = runExceptT acts >>= either pure pure

simplify
    :: (MonadCatch m, MonadSimplify m)
    => Lens' goal (RulePattern VariableName)
    -> goal
    -> Strategy.TransitionT (Rule goal) m goal
simplify lensRulePattern =
    Lens.traverseOf (lensRulePattern . RulePattern.leftPattern) $ \config ->
    withConfiguration config $ do
        configs <-
            simplifyTopConfiguration config >>= SMT.Evaluator.filterMultiOr
            & lift
        if isBottom configs
            then pure Pattern.bottom
            else Foldable.asum (pure <$> configs)

isTriviallyValid :: Lens' goal (RulePattern variable) -> goal -> Bool
isTriviallyValid lensRulePattern =
    isBottom . RulePattern.left . Lens.view lensRulePattern

isTrusted :: From goal Attribute.Axiom.Trusted => goal -> Bool
isTrusted = Attribute.Trusted.isTrusted . from @_ @Attribute.Axiom.Trusted

-- | Exception that contains the last configuration before the error.
data WithConfiguration = WithConfiguration (Pattern VariableName) SomeException
    deriving (Show, Typeable)

instance Exception WithConfiguration

-- | Apply 'Rule's to the goal in parallel.
derivePar
    :: forall m goal
    .  (MonadCatch m, MonadSimplify m)
    => ProofState.ProofState goal ~ ProofState goal goal
    => Lens' goal (RulePattern VariableName)
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
derivePar lensRulePattern mkRule =
    deriveWith lensRulePattern mkRule
    $ Step.applyRewriteRulesParallel Unification.unificationProcedure

type Deriver monad =
        [RewriteRule RewritingVariableName]
    ->  Pattern VariableName
    ->  monad (Step.Results RulePattern VariableName)

-- | Apply 'Rule's to the goal in parallel.
deriveWith
    :: forall m goal
    .  MonadCatch m
    => ProofState.ProofState goal ~ ProofState goal goal
    => Lens' goal (RulePattern VariableName)
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> Deriver m
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
deriveWith lensRulePattern mkRule takeStep rewrites goal =
    (\x -> getCompose $ x goal)
    $ Lens.traverseOf (lensRulePattern . RulePattern.leftPattern)
    $ \config -> Compose $ withConfiguration config $ do
        results <- takeStep rewrites config & lift
        deriveResults mkRule results

-- | Apply 'Rule's to the goal in sequence.
deriveSeq
    :: forall m goal
    .  (MonadCatch m, MonadSimplify m)
    => ProofState.ProofState goal ~ ProofState goal goal
    => Lens' goal (RulePattern VariableName)
    -> (RewriteRule RewritingVariableName -> Rule goal)
    -> [RewriteRule RewritingVariableName]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
deriveSeq lensRulePattern mkRule =
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

withConfiguration :: MonadCatch m => Pattern VariableName -> m a -> m a
withConfiguration configuration =
    handle (throw . WithConfiguration configuration)

{- | The predicate to remove the destination from the present configuration.
 -}
removalPredicate
    :: forall variable m
    .  InternalVariable variable
    => MonadSimplify m
    => Pattern variable
    -- ^ Destination
    -> Pattern variable
    -- ^ Current configuration
    -> m (Predicate variable)
removalPredicate
    destination
    configuration
  | isFunctionPattern configTerm
  , isFunctionPattern destTerm
  = do
    -- TODO (thomas.tuegel): Use unification here, not simplification.
    unifiedConfigs <-
        simplifyConditionalTermToOr sideCondition (mkAnd configTerm destTerm)
    case OrPattern.toPatterns unifiedConfigs of
        _ | OrPattern.isFalse unifiedConfigs ->
            return Predicate.makeTruePredicate_
        [substPattern] -> do
            let extraElemVariables =
                    getExtraElemVariables configuration substPattern
                remainderPattern =
                    Pattern.fromCondition
                    . Conditional.withoutTerm
                    $ (const <$> destination <*> substPattern)
            evaluatedRemainder <-
                Exists.makeEvaluate
                    sideCondition extraElemVariables remainderPattern
            return
                . Predicate.makeNotPredicate
                . Condition.toPredicate
                . Conditional.withoutTerm
                . OrPattern.toPattern
                $ evaluatedRemainder
        _ ->
            error . show . Pretty.vsep $
            [ "Unifying the terms of the configuration and the\
            \ destination has unexpectedly produced more than one\
            \ unification case."
            , Pretty.indent 2 "Unification cases:"
            ]
            <> fmap
                (Pretty.indent 4 . unparse)
                (Foldable.toList unifiedConfigs)
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
    -- The variables of the destination that are missing from the
    -- configuration. These are the variables which should be existentially
    -- quantified in the removal predicate.
    getExtraElemVariables config dest =
        let extraNonElemVariables = remainderNonElemVariables config dest
        in if not . null $ extraNonElemVariables
            then
                error . show . Pretty.vsep $
                    "Cannot quantify non-element variables: "
                    : fmap (Pretty.indent 4 . unparse) extraNonElemVariables
            else remainderElementVariables config dest
    configVariables :: Pattern variable -> Set.Set (SomeVariable variable)
    configVariables = FreeVariables.toSet . freeVariables
    destVariables = FreeVariables.toSet . freeVariables
    remainderVariables config dest =
        Set.toList
        $ Set.difference
            (destVariables dest)
            (configVariables config)
    remainderNonElemVariables config dest =
        filter (not . isElementVariable) (remainderVariables config dest)
    remainderElementVariables config dest =
        mapMaybe
            retractElementVariable
            (remainderVariables config dest)

getConfiguration :: ReachabilityRule -> Pattern VariableName
getConfiguration (toRulePattern -> RulePattern { left, requires }) =
    Pattern.withCondition left (Conditional.fromPredicate requires)

getDestination :: ReachabilityRule -> RHS VariableName
getDestination (toRulePattern -> RulePattern { rhs }) = rhs

class ToReachabilityRule rule where
    toReachabilityRule :: rule -> ReachabilityRule

instance ToReachabilityRule OnePathRule where
    toReachabilityRule = OnePath

instance ToReachabilityRule AllPathRule where
    toReachabilityRule = AllPath

instance ToReachabilityRule ReachabilityRule where
    toReachabilityRule = id

debugProofStateBracket
    :: forall monad goal
    .  MonadLog monad
    => ToReachabilityRule goal
    => Coercible (Rule goal) (RewriteRule RewritingVariableName)
    => ProofState goal goal ~ ProofState.ProofState goal
    => Prim goal ~ ProofState.Prim (Rule goal)
    => ProofState goal goal
    -- ^ current proof state
    -> Prim goal
    -- ^ transition
    -> monad (ProofState goal goal)
    -- ^ action to be computed
    -> monad (ProofState goal goal)
debugProofStateBracket
    (fmap toReachabilityRule -> proofState)
    (coerce -> transition)
    action
  = do
    result <- action
    logEntry DebugProofState
        { proofState
        , transition
        , result = Just $ toReachabilityRule <$> result
        }
    return result

debugProofStateFinal
    :: forall monad goal
    .  Alternative monad
    => MonadLog monad
    => ToReachabilityRule goal
    => Coercible (Rule goal) (RewriteRule RewritingVariableName)
    => ProofState goal goal ~ ProofState.ProofState goal
    => Prim goal ~ ProofState.Prim (Rule goal)
    => ProofState goal goal
    -- ^ current proof state
    -> Prim goal
    -- ^ transition
    -> monad (ProofState goal goal)
debugProofStateFinal
    (fmap toReachabilityRule -> proofState)
    (coerce -> transition)
  = do
    logEntry DebugProofState
        { proofState
        , transition
        , result = Nothing
        }
    empty

withDebugProofState
    :: forall monad goal
    .  MonadLog monad
    => ToReachabilityRule goal
    => Coercible (Rule goal) (RewriteRule RewritingVariableName)
    => ProofState goal goal ~ ProofState.ProofState goal
    => Prim goal ~ ProofState.Prim (Rule goal)
    =>
        (  Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) monad (ProofState goal goal)
        )
    ->
        (  Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) monad (ProofState goal goal)
        )
withDebugProofState transitionFunc =
    \transition state ->
        Transition.orElse
            (debugProofStateBracket
                state
                transition
                (transitionFunc transition state)
            )
            (debugProofStateFinal
                state
                transition
            )
