{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.Goal
    ( Goal (..)
    , ToRulePattern (..)
    , FromRulePattern (..)
    , ClaimExtractor (..)
    , Rule (..)
    , TransitionRuleTemplate (..)
    , WithConfiguration (..)
    , extractClaims
    , unprovenNodes
    , proven
    , onePathFirstStep
    , onePathFollowupStep
    , allPathFirstStep
    , allPathFollowupStep
    , configurationDestinationToRule
    , getConfiguration
    , getDestination
    , transitionRuleTemplate
    , isTrusted
    ) where

import Prelude.Kore

import Control.Exception
    ( throw
    )
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
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import Data.List.Extra
    ( groupSortOn
    , sortOn
    )
import qualified Data.Set as Set
import Data.Stream.Infinite
    ( Stream (..)
    )
import qualified Data.Stream.Infinite as Stream
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP
import GHC.Generics as GHC

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import Kore.Attribute.Pattern.FreeVariables
    ( freeVariables
    )
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute.FreeVariables
import qualified Kore.Attribute.Trusted as Attribute.Trusted
import Kore.Debug
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
    ( isFunctionPattern
    , mkAnd
    )
import Kore.Log.DebugProofState
import qualified Kore.Profiler.Profile as Profile
    ( timeStrategy
    )
import qualified Kore.Step.Result as Result
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
import qualified Kore.Step.Transition as Transition
import Kore.Strategies.ProofState hiding
    ( Prim
    , ProofState
    , proofState
    )
import qualified Kore.Strategies.ProofState as ProofState
import qualified Kore.Syntax.Sentence as Syntax
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.TopBottom
    ( isBottom
    , isTop
    )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.UnifierT as Monad.Unify
import Kore.Unparser
    ( Unparse
    , unparse
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    , extractElementVariable
    , isElemVar
    )
import qualified Kore.Verified as Verified
import Log
    ( MonadLog (..)
    )

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
    data Rule goal
    type Prim goal
    type ProofState goal a

    goalToRule :: goal -> Rule goal
    default goalToRule
        :: Coercible goal (Rule goal)
        => goal -> Rule goal
    goalToRule = coerce

    -- | Since Goals usually carry more information than Rules,
    -- we need to know the context when transforming a Rule into a Goal,
    -- hence the first 'goal' argument. In general it can be ignored
    -- when the Goal and the Rule are representationally equal.
    ruleToGoal :: goal -> Rule goal -> goal
    default ruleToGoal
        :: Coercible (Rule goal) goal
        => goal -> Rule goal -> goal
    ruleToGoal _ = coerce

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

class ClaimExtractor claim where
    extractClaim
        :: (Attribute.Axiom.Axiom Symbol Variable, Verified.SentenceClaim)
        -> Maybe (Attribute.Axiom.Axiom Symbol Variable, claim)

-- | Extracts all One-Path claims from a verified module.
extractClaims
    :: ClaimExtractor claim
    => VerifiedModule declAtts
    -- ^'IndexedModule' containing the definition
    -> [(Attribute.Axiom.Axiom Symbol Variable, claim)]
extractClaims idxMod =
    mapMaybe
        -- applying on second component
        extractClaim
        (indexedModuleClaims idxMod)

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

instance Goal (OnePathRule Variable) where

    newtype Rule (OnePathRule Variable) =
        OnePathRewriteRule { unRule :: RewriteRule Variable }
        deriving (GHC.Generic, Show, Unparse)

    type Prim (OnePathRule Variable) =
        ProofState.Prim (Rule (OnePathRule Variable))

    type ProofState (OnePathRule Variable) a =
        ProofState.ProofState a

    transitionRule =
        withDebugProofState
        $ transitionRuleTemplate
            TransitionRuleTemplate
                { simplifyTemplate =
                    simplify
                , removeDestinationTemplate =
                    removeDestination
                , isTriviallyValidTemplate =
                    isTriviallyValid
                , deriveParTemplate =
                    derivePar
                , deriveSeqTemplate =
                    deriveSeq
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
        rewrites =
            sortOn
                (RulePattern.getPriorityOfRule . toRulePattern)
                rules
        coinductiveRewrites =
            OnePathRewriteRule
            . RewriteRule
            . getOnePathRule
            <$> goals

instance SOP.Generic (Rule (OnePathRule Variable))

instance SOP.HasDatatypeInfo (Rule (OnePathRule Variable))

instance Debug (Rule (OnePathRule Variable))

instance Diff (Rule (OnePathRule Variable))

instance ToRulePattern (Rule (OnePathRule Variable))

instance FromRulePattern (Rule (OnePathRule Variable))

instance ClaimExtractor (OnePathRule Variable) where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (OnePathClaimPattern claim) -> Just (attrs, claim)
            _ -> Nothing

instance Goal (AllPathRule Variable) where

    newtype Rule (AllPathRule Variable) =
        AllPathRewriteRule { unRule :: RewriteRule Variable }
        deriving (GHC.Generic, Show, Unparse)

    type Prim (AllPathRule Variable) =
        ProofState.Prim (Rule (AllPathRule Variable))

    type ProofState (AllPathRule Variable) a =
        ProofState.ProofState a

    transitionRule =
        withDebugProofState
        $ transitionRuleTemplate
            TransitionRuleTemplate
                { simplifyTemplate =
                    simplify
                , removeDestinationTemplate =
                    removeDestination
                , isTriviallyValidTemplate =
                    isTriviallyValid
                , deriveParTemplate =
                    derivePar
                , deriveSeqTemplate =
                    deriveSeq
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
        priorityGroups =
            groupSortOn
                (RulePattern.getPriorityOfRule . toRulePattern)
                rules
        coinductiveRewrites =
            AllPathRewriteRule
            . RewriteRule
            . getAllPathRule
            <$> goals

instance SOP.Generic (Rule (AllPathRule Variable))

instance SOP.HasDatatypeInfo (Rule (AllPathRule Variable))

instance Debug (Rule (AllPathRule Variable))

instance Diff (Rule (AllPathRule Variable))

instance ToRulePattern (Rule (AllPathRule Variable))

instance FromRulePattern (Rule (AllPathRule Variable))

instance ClaimExtractor (AllPathRule Variable) where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (AllPathClaimPattern claim) -> Just (attrs, claim)
            _ -> Nothing

instance Goal (ReachabilityRule Variable) where

    newtype Rule (ReachabilityRule Variable) =
        ReachabilityRewriteRule
            { unReachabilityRewriteRule :: RewriteRule Variable }
        deriving (GHC.Generic, Show, Unparse)

    type Prim (ReachabilityRule Variable) =
        ProofState.Prim (Rule (ReachabilityRule Variable))

    type ProofState (ReachabilityRule Variable) a =
        ProofState.ProofState a

    goalToRule (OnePath rule) = coerce rule
    goalToRule (AllPath rule) = coerce rule

    ruleToGoal (OnePath _) rule = OnePath (coerce rule)
    ruleToGoal (AllPath _) rule = AllPath (coerce rule)

    transitionRule
        :: (MonadCatch m, MonadSimplify m)
        => Prim (ReachabilityRule Variable)
        -> ProofState
            (ReachabilityRule Variable)
            (ReachabilityRule Variable)
        -> Strategy.TransitionT
            (Rule (ReachabilityRule Variable))
            m
            ( ProofState
                (ReachabilityRule Variable)
                (ReachabilityRule Variable)
            )
    transitionRule prim proofstate =
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
                    CheckGoalStuck ->
                        debugProofStateFinal
                            state
                            CheckGoalStuck
                    _ -> return proofstate
            Proven ->
                case prim of
                    CheckProven ->
                        debugProofStateFinal
                            Proven
                            CheckProven
                    _ -> return proofstate

    strategy
        :: ReachabilityRule Variable
        -> [ReachabilityRule Variable]
        -> [Rule (ReachabilityRule Variable)]
        -> Stream (Strategy (Prim (ReachabilityRule Variable)))
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

instance SOP.Generic (Rule (ReachabilityRule Variable))

instance SOP.HasDatatypeInfo (Rule (ReachabilityRule Variable))

instance Debug (Rule (ReachabilityRule Variable))

instance Diff (Rule (ReachabilityRule Variable))

instance ToRulePattern (Rule (ReachabilityRule Variable))

instance FromRulePattern (Rule (ReachabilityRule Variable))

instance ClaimExtractor (ReachabilityRule Variable) where
    extractClaim (attrs, sentence) =
        case fromSentenceAxiom (attrs, Syntax.getSentenceClaim sentence) of
            Right (OnePathClaimPattern claim) -> Just (attrs, OnePath claim)
            Right (AllPathClaimPattern claim) -> Just (attrs, AllPath claim)
            _ -> Nothing

maybeOnePath :: ReachabilityRule Variable -> Maybe (OnePathRule Variable)
maybeOnePath (OnePath rule) = Just rule
maybeOnePath _ = Nothing

maybeAllPath :: ReachabilityRule Variable -> Maybe (AllPathRule Variable)
maybeAllPath (AllPath rule) = Just rule
maybeAllPath _ = Nothing

reachabilityOnePathStrategy
    :: Functor t
    => t (Strategy (Prim (OnePathRule Variable)))
    -> t (Strategy (Prim (ReachabilityRule Variable)))
reachabilityOnePathStrategy strategy' =
    (fmap . fmap . fmap)
        ruleOnePathToRuleReachability
        strategy'

reachabilityAllPathStrategy
    :: Functor t
    => t (Strategy (Prim (AllPathRule Variable)))
    -> t (Strategy (Prim (ReachabilityRule Variable)))
reachabilityAllPathStrategy strategy' =
    (fmap . fmap . fmap)
        ruleAllPathToRuleReachability
        strategy'

allPathProofState
    :: ProofState (AllPathRule Variable) (AllPathRule Variable)
    -> ProofState (ReachabilityRule Variable) (ReachabilityRule Variable)
allPathProofState = fmap AllPath

onePathProofState
    :: ProofState (OnePathRule Variable) (OnePathRule Variable)
    -> ProofState (ReachabilityRule Variable) (ReachabilityRule Variable)
onePathProofState = fmap OnePath

primRuleOnePath
    :: ProofState.Prim (Rule (ReachabilityRule Variable))
    -> ProofState.Prim (Rule (OnePathRule Variable))
primRuleOnePath = fmap ruleReachabilityToRuleOnePath

primRuleAllPath
    :: ProofState.Prim (Rule (ReachabilityRule Variable))
    -> ProofState.Prim (Rule (AllPathRule Variable))
primRuleAllPath = fmap ruleReachabilityToRuleAllPath

-- The functions below are easier to read coercions between
-- the newtypes over 'RewriteRule Variable' defined in the
-- instances of 'Goal' as 'Rule's.
ruleReachabilityToRuleAllPath
    :: Rule (ReachabilityRule Variable)
    -> Rule (AllPathRule Variable)
ruleReachabilityToRuleAllPath = coerce

ruleReachabilityToRuleOnePath
    :: Rule (ReachabilityRule Variable)
    -> Rule (OnePathRule Variable)
ruleReachabilityToRuleOnePath = coerce

ruleAllPathToRuleReachability
    :: Rule (AllPathRule Variable)
    -> Rule (ReachabilityRule Variable)
ruleAllPathToRuleReachability = coerce

ruleOnePathToRuleReachability
    :: Rule (OnePathRule Variable)
    -> Rule (ReachabilityRule Variable)
ruleOnePathToRuleReachability = coerce

data TransitionRuleTemplate monad goal =
    TransitionRuleTemplate
    { simplifyTemplate
        :: goal -> Strategy.TransitionT (Rule goal) monad goal
    , removeDestinationTemplate
        :: (goal -> ProofState goal goal)
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
        Profile.timeStrategy "Goal.Simplify"
        $ Goal <$> simplifyTemplate goal
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
    :: [[Rule (AllPathRule Variable)]]
    -> [Prim (AllPathRule Variable)]
groupStrategy [] =
    [DerivePar [], Simplify, TriviallyValid]
groupStrategy axiomGroups = do
    group <- axiomGroups
    [DerivePar group, Simplify, TriviallyValid]

allPathFirstStep
    :: [[Rule (AllPathRule Variable)]]
    -> Strategy (Prim (AllPathRule Variable))
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
    :: [Rule (AllPathRule Variable)]
    -> [[Rule (AllPathRule Variable)]]
    -> Strategy (Prim (AllPathRule Variable))
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
    :: MonadSimplify m
    => MonadCatch m
    => ProofState.ProofState goal ~ ProofState goal goal
    => ToRulePattern goal
    => (goal -> ProofState goal goal)
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
removeDestination stateConstructor goal =
    withConfiguration goal $ lift $ do
        removal <- removalPredicate destination configuration
        if isTop removal
            then return . stateConstructor $ goal
            else do
                simplifiedRemoval <-
                    SMT.Evaluator.filterMultiOr
                    =<< simplifyTopConfiguration
                        (Conditional.andPredicate configuration removal)
                if not (isBottom simplifiedRemoval)
                    then return . GoalStuck $ goal
                    else return Proven
  where
    configuration = getConfiguration goal
    configFreeVars = freeVariables configuration

    RulePattern { rhs } = toRulePattern goal

    destination = topExistsToImplicitForall configFreeVars rhs

simplify
    :: (MonadCatch m, MonadSimplify m)
    => ToRulePattern goal
    => FromRulePattern goal
    => goal
    -> Strategy.TransitionT (Rule goal) m goal
simplify goal = withConfiguration goal $ do
    configs <- lift $
        simplifyTopConfiguration configuration
    filteredConfigs <- SMT.Evaluator.filterMultiOr configs
    if null filteredConfigs
        then pure $ configurationDestinationToRule goal Pattern.bottom destination
        else do
            let simplifiedRules =
                    fmap (flip (configurationDestinationToRule goal) destination) filteredConfigs
            Foldable.asum (pure <$> simplifiedRules)
  where
    destination = getDestination goal
    configuration = getConfiguration goal

isTriviallyValid
    :: ToRulePattern goal
    => goal -> Bool
isTriviallyValid = isBottom . RulePattern.left . toRulePattern

isTrusted
    :: forall goal
    .  ToRulePattern goal
    => goal -> Bool
isTrusted =
    Attribute.Trusted.isTrusted
    . Attribute.Axiom.trusted
    . RulePattern.attributes
    . toRulePattern

-- | Exception that contains the last configuration before the error.
data WithConfiguration = WithConfiguration (Pattern Variable) SomeException
    deriving (Show, Typeable)

instance Exception WithConfiguration

-- | Apply 'Rule's to the goal in parallel.
derivePar
    :: forall m goal
    .  (MonadCatch m, MonadSimplify m)
    => Goal goal
    => ProofState.ProofState goal ~ ProofState goal goal
    => ToRulePattern goal
    => FromRulePattern goal
    => ToRulePattern (Rule goal)
    => FromRulePattern (Rule goal)
    => [Rule goal]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
derivePar rules goal = withConfiguration goal $ do
    let rewrites = RewriteRule . toRulePattern <$> rules
    eitherResults <-
        lift . Monad.Unify.runUnifierT
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
        Right results -> deriveResults goal results
  where
    configuration :: Pattern Variable
    configuration = getConfiguration goal

-- | Apply 'Rule's to the goal in sequence.
deriveSeq
    :: forall m goal
    .  (MonadCatch m, MonadSimplify m)
    => Goal goal
    => ProofState.ProofState goal ~ ProofState goal goal
    => ToRulePattern goal
    => FromRulePattern goal
    => ToRulePattern (Rule goal)
    => FromRulePattern (Rule goal)
    => [Rule goal]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
deriveSeq rules goal = withConfiguration goal $ do
    let rewrites = RewriteRule . toRulePattern <$> rules
    eitherResults <-
        lift . Monad.Unify.runUnifierT
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
        Right results -> deriveResults goal results
  where
    configuration = getConfiguration goal

deriveResults
    :: MonadSimplify simplifier
    => (Goal goal, FromRulePattern goal, ToRulePattern goal)
    => FromRulePattern (Rule goal)
    => goal
    -> [Step.Results RulePattern Variable]
    -> Strategy.TransitionT (Rule goal) simplifier (ProofState.ProofState goal)
deriveResults goal results = do
    let mapRules =
            Result.mapRules
            $ (fromRulePattern . goalToRule $ goal)
            . Step.unTargetRule
            . Step.withoutUnification
        traverseConfigs =
            Result.traverseConfigs
                (pure . GoalRewritten)
                (pure . GoalRemainder)
    let onePathResults =
            Result.mapConfigs
                (flip (configurationDestinationToRule goal) destination)
                (flip (configurationDestinationToRule goal) destination)
                (Result.mergeResults results)
    results' <-
        traverseConfigs (mapRules onePathResults)
    Result.transitionResults results'
  where
    destination = getDestination goal

withConfiguration :: MonadCatch m => ToRulePattern goal => goal -> m a -> m a
withConfiguration goal = handle (throw . WithConfiguration configuration)
  where
    configuration = getConfiguration goal

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
    configVariables :: Pattern variable -> Set.Set (UnifiedVariable variable)
    configVariables config =
        Attribute.FreeVariables.getFreeVariables
        $ freeVariables config
    destVariables dest =
        Attribute.FreeVariables.getFreeVariables
        $ freeVariables dest
    remainderVariables config dest =
        Set.toList
        $ Set.difference
            (destVariables dest)
            (configVariables config)
    remainderNonElemVariables config dest =
        filter (not . isElemVar) (remainderVariables config dest)
    remainderElementVariables config dest =
        mapMaybe
            extractElementVariable
            (remainderVariables config dest)

getConfiguration
    :: forall goal
    .  ToRulePattern goal
    => goal
    -> Pattern Variable
getConfiguration (toRulePattern -> RulePattern { left, requires }) =
    Pattern.withCondition left (Conditional.fromPredicate requires)

getDestination
    :: forall goal
    .  ToRulePattern goal
    => goal
    -> RHS Variable
getDestination (toRulePattern -> RulePattern { rhs }) = rhs

{-| Given a rule to use as a prototype, a 'Pattern' to use as the configuration
and a 'RHS' containing the destination, makes a rule out of them.
-}
configurationDestinationToRule
    :: forall rule
    .  FromRulePattern rule
    => rule
    -> Pattern Variable
    -> RHS Variable
    -> rule
configurationDestinationToRule ruleType configuration rhs =
    let (left, Condition.toPredicate -> requires) =
            Pattern.splitTerm configuration
    in fromRulePattern ruleType $ RulePattern
        { left
        , antiLeft = Nothing
        , requires
        , rhs
        , attributes = Default.def
        }

class ToReachabilityRule rule where
    toReachabilityRule :: rule -> ReachabilityRule Variable

instance ToReachabilityRule (OnePathRule Variable) where
    toReachabilityRule = OnePath

instance ToReachabilityRule (AllPathRule Variable) where
    toReachabilityRule = AllPath

instance ToReachabilityRule (ReachabilityRule Variable) where
    toReachabilityRule = id

debugProofStateBracket
    :: forall monad goal
    .  MonadLog monad
    => ToReachabilityRule goal
    => Coercible (Rule goal) (RewriteRule Variable)
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
    => Coercible (Rule goal) (RewriteRule Variable)
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
    => Coercible (Rule goal) (RewriteRule Variable)
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
