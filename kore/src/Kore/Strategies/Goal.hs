{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.Goal
    ( Goal (..)
    , Rule (..)
    , TransitionRuleTemplate (..)
    , unprovenNodes
    , proven
    , onePathFirstStep
    , onePathFollowupStep
    , allPathFirstStep
    , allPathFollowupStep
    , makeRuleFromPatterns
    , getConfiguration
    , getDestination
    , transitionRuleTemplate
    , isTrusted
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Monad.Catch
    ( MonadCatch
    , onException
    )
import qualified Control.Monad.Trans as Monad.Trans
import Data.Coerce
    ( Coercible
    , coerce
    )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import Data.Maybe
    ( mapMaybe
    )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import GHC.Generics as GHC

import Debug
    ( formatExceptionInfo
    )
import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute.FreeVariables
import qualified Kore.Attribute.Trusted as Attribute.Trusted
import Kore.Debug
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( mkAnd
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Profiler.Profile as Profile
    ( timeStrategy
    )
import qualified Kore.Step.Result as Result
import Kore.Step.Rule
    ( AllPathRule (..)
    , OnePathRule (..)
    , RewriteRule (..)
    , RulePattern (..)
    )
import qualified Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    )
import Kore.Step.Simplification.Data
    ( MonadSimplify
    , SimplifierVariable
    )
import Kore.Step.Simplification.Pattern
    ( simplifyAndRemoveTopExists
    )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import qualified Kore.Step.Step as Step
import Kore.Step.Strategy
    ( Strategy
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Strategies.ProofState hiding
    ( Prim
    , ProofState
    )
import qualified Kore.Strategies.ProofState as ProofState
import Kore.TopBottom
    ( isBottom
    )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser
    ( Unparse
    , unparse
    , unparseToText
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (ElemVar)
    , isElemVar
    )

{- | The final nodes of an execution graph which were not proven.

See also: 'Strategy.pickFinal', 'extractUnproven'

 -}
unprovenNodes
    :: forall goal a
    .  Goal goal
    => ProofState.ProofState a ~ ProofState goal a
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
    .  Goal goal
    => ProofState.ProofState a ~ ProofState goal a
    => Strategy.ExecutionGraph (ProofState goal a) (Rule goal)
    -> Bool
proven = Foldable.null . unprovenNodes

class Goal goal where
    data Rule goal
    type Prim goal
    type ProofState goal a

    transitionRule
        :: (MonadCatch m, MonadSimplify m)
        => Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)

    strategy
        :: [goal]
        -> [Rule goal]
        -> [Strategy (Prim goal)]

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

instance (SimplifierVariable variable) => Goal (OnePathRule variable) where

    newtype Rule (OnePathRule variable) =
        OnePathRewriteRule { unRule :: RewriteRule variable }
        deriving (GHC.Generic, Show, Unparse)

    type Prim (OnePathRule variable) =
        ProofState.Prim (Rule (OnePathRule variable))

    type ProofState (OnePathRule variable) a =
        ProofState.ProofState a

    transitionRule =
        transitionRuleTemplate
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

    strategy goals rules =
        onePathFirstStep rewrites
        : repeat
            ( onePathFollowupStep
                coinductiveRewrites
                rewrites
            )
      where
        rewrites = rules
        coinductiveRewrites =
            OnePathRewriteRule
            . RewriteRule
            . getOnePathRule
            <$> goals

instance SOP.Generic (Rule (OnePathRule variable))

instance SOP.HasDatatypeInfo (Rule (OnePathRule variable))

instance Debug variable => Debug (Rule (OnePathRule variable))

instance (Debug variable, Diff variable) => Diff (Rule (OnePathRule variable))

instance (SimplifierVariable variable) => Goal (AllPathRule variable) where

    newtype Rule (AllPathRule variable) =
        AllPathRewriteRule { unRule :: RewriteRule variable }
        deriving (GHC.Generic, Show, Unparse)

    type Prim (AllPathRule variable) =
        ProofState.Prim (Rule (AllPathRule variable))

    type ProofState (AllPathRule variable) a =
        ProofState.ProofState a

    transitionRule =
        transitionRuleTemplate
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

    strategy goals rules =
        allPathFirstStep rewrites
        : repeat
            ( allPathFollowupStep
                coinductiveRewrites
                rewrites
            )
      where
        rewrites = rules
        coinductiveRewrites =
            AllPathRewriteRule
            . RewriteRule
            . getAllPathRule
            <$> goals

instance SOP.Generic (Rule (AllPathRule variable))

instance SOP.HasDatatypeInfo (Rule (AllPathRule variable))

instance Debug variable => Debug (Rule (AllPathRule variable))

instance (Debug variable, Diff variable) => Diff (Rule (AllPathRule variable))

data TransitionRuleTemplate monad goal =
    TransitionRuleTemplate
    { simplifyTemplate
        :: goal -> Strategy.TransitionT (Rule goal) monad goal
    , removeDestinationTemplate
        :: goal -> Strategy.TransitionT (Rule goal) monad goal
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
    => Goal goal
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

    transitionRuleWorker ResetGoal (GoalRewritten goal) = return (Goal goal)

    transitionRuleWorker Simplify (Goal g) =
        Profile.timeStrategy "Goal.Simplify"
        $ Goal <$> simplifyTemplate g
    transitionRuleWorker Simplify (GoalRemainder g) =
        Profile.timeStrategy "Goal.SimplifyRemainder"
        $ GoalRemainder <$> simplifyTemplate g

    transitionRuleWorker RemoveDestination (Goal g) =
        Profile.timeStrategy "Goal.RemoveDestination"
        $ Goal <$> removeDestinationTemplate g
    transitionRuleWorker RemoveDestination (GoalRemainder g) =
        Profile.timeStrategy "Goal.RemoveDestinationRemainder"
        $ GoalRemainder <$> removeDestinationTemplate g

    transitionRuleWorker TriviallyValid (Goal g)
      | isTriviallyValidTemplate g = return Proven
    transitionRuleWorker TriviallyValid (GoalRemainder g)
      | isTriviallyValidTemplate g = return Proven
    transitionRuleWorker TriviallyValid (GoalRewritten g)
      | isTriviallyValidTemplate g = return Proven

    transitionRuleWorker (DerivePar rules) (Goal g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        --
        -- Note that in most transitions it is obvious what is being transformed
        -- into what, e.g. that a `ResetGoal` transition transforms
        -- `GoalRewritten` into `Goal`. However, here we're taking a `Goal`
        -- and transforming it into `GoalRewritten` and `GoalRemainder` in an
        -- opaque way. I think that there's no good reason for wrapping the
        -- results in `derivePar` as opposed to here.
        Profile.timeStrategy "Goal.DerivePar"
        $ deriveParTemplate rules g
    transitionRuleWorker (DerivePar rules) (GoalRemainder g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        -- See above for an explanation.
        Profile.timeStrategy "Goal.DeriveParRemainder"
        $ deriveParTemplate rules g

    transitionRuleWorker (DeriveSeq rules) (Goal g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        -- See above for an explanation.
        Profile.timeStrategy "Goal.DeriveSeq"
        $ deriveSeqTemplate rules g
    transitionRuleWorker (DeriveSeq rules) (GoalRemainder g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        -- See above for an explanation.
        Profile.timeStrategy "Goal.DeriveSeqRemainder"
        $ deriveSeqTemplate rules g

    transitionRuleWorker _ state = return state

-- TODO(Ana): could be less general when all-path will be connected to repl
onePathFirstStep
    :: Goal goal
    => ProofState goal goal ~ ProofState.ProofState goal
    => Prim goal ~ ProofState.Prim (Rule goal)
    => [Rule goal]
    -> Strategy (Prim goal)
onePathFirstStep axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq axioms
        , Simplify
        , TriviallyValid
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

-- TODO(Ana): could be less general when all-path will be connected to repl
onePathFollowupStep
    :: Goal goal
    => ProofState goal goal ~ ProofState.ProofState goal
    => Prim goal ~ ProofState.Prim (Rule goal)
    => [Rule goal]
    -> [Rule goal]
    -> Strategy (Prim goal)
onePathFollowupStep claims axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
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

allPathFirstStep
    :: [Rule (AllPathRule variable)]
    -> Strategy (Prim (AllPathRule variable))
allPathFirstStep axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DerivePar axioms
        , Simplify
        , TriviallyValid
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

allPathFollowupStep
    :: [Rule (AllPathRule variable)]
    -> [Rule (AllPathRule variable)]
    -> Strategy (Prim (AllPathRule variable))
allPathFollowupStep claims axioms =
    (Strategy.sequence . map Strategy.apply)
        [ CheckProven
        , CheckGoalRemainder
        , Simplify
        , TriviallyValid
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq claims
        , Simplify
        , TriviallyValid
        , DerivePar axioms
        , Simplify
        , TriviallyValid
        , ResetGoal
        , Simplify
        , TriviallyValid
        ]

-- | Remove the destination of the goal.
removeDestination
    :: (MonadCatch m, MonadSimplify m)
    => Goal goal
    => SimplifierVariable variable
    => Coercible goal (RulePattern variable)
    => goal
    -> Strategy.TransitionT (Rule goal) m goal
removeDestination goal = errorBracket $ do
    let removal = removalPredicate destination configuration
        result = Conditional.andPredicate configuration removal
    pure $ makeRuleFromPatterns result destination
  where
    destination = getDestination goal
    configuration = getConfiguration goal

    errorBracket action =
        onException action
            (formatExceptionInfo
                ("configuration=" <> unparseToText configuration)
            )

simplify
    :: (MonadCatch m, MonadSimplify m)
    => Goal goal
    => SimplifierVariable variable
    => Coercible goal (RulePattern variable)
    => goal
    -> Strategy.TransitionT (Rule goal) m goal
simplify goal = errorBracket $ do
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
  where
    destination = getDestination goal
    configuration = getConfiguration goal

    errorBracket action =
        onException action
            (formatExceptionInfo
                ("configuration=" <> unparseToText configuration)
            )

isTriviallyValid
    :: SimplifierVariable variable
    => Goal goal
    => Coercible goal (RulePattern variable)
    => goal -> Bool
isTriviallyValid = isBottom . RulePattern.left . coerce

isTrusted
    :: SimplifierVariable variable
    => Goal goal
    => Coercible goal (RulePattern variable)
    => goal -> Bool
isTrusted =
    Attribute.Trusted.isTrusted
    . Attribute.Axiom.trusted
    . RulePattern.attributes
    . coerce

-- | Apply 'Rule's to the goal in parallel.
derivePar
    :: forall m goal variable
    .  (MonadCatch m, MonadSimplify m)
    => Goal goal
    => ProofState.ProofState goal ~ ProofState goal goal
    => SimplifierVariable variable
    => Coercible goal (RulePattern variable)
    => Coercible (RulePattern variable) goal
    => Coercible (Rule goal) (RulePattern variable)
    => Coercible (RulePattern variable) (Rule goal)
    => [Rule goal]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
derivePar rules goal = errorBracket $ do
    let rewrites = coerce <$> rules
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
                        (pure . GoalRewritten)
                        (pure . GoalRemainder)
            let onePathResults =
                    Result.mapConfigs
                        (`makeRuleFromPatterns` destination)
                        (`makeRuleFromPatterns` destination)
                        (Result.mergeResults results)
            results' <-
                traverseConfigs (mapRules onePathResults)
            Result.transitionResults results'
  where
    destination = getDestination goal
    configuration :: Pattern variable
    configuration = getConfiguration goal

    errorBracket action =
        onException action
            (formatExceptionInfo
                ("configuration=" <> unparseToText configuration)
            )

-- | Apply 'Rule's to the goal in sequence.
deriveSeq
    :: forall m goal variable
    .  (MonadCatch m, MonadSimplify m)
    => Goal goal
    => ProofState.ProofState goal ~ ProofState goal goal
    => SimplifierVariable variable
    => Coercible goal (RulePattern variable)
    => Coercible (RulePattern variable) goal
    => Coercible (Rule goal) (RulePattern variable)
    => Coercible (RulePattern variable) (Rule goal)
    => [Rule goal]
    -> goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
deriveSeq rules goal = errorBracket $ do
    let rewrites = coerce <$> rules
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
                        (pure . GoalRewritten)
                        (pure . GoalRemainder)
            let onePathResults =
                    Result.mapConfigs
                        (`makeRuleFromPatterns` destination)
                        (`makeRuleFromPatterns` destination)
                        (Result.mergeResults results)
            results' <-
                traverseConfigs (mapRules onePathResults)
            Result.transitionResults results'
  where
    destination = getDestination goal
    configuration = getConfiguration goal

    errorBracket action =
        onException action
            (formatExceptionInfo
                ("configuration=" <> unparseToText configuration)
            )

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
        { left
        , antiLeft = Nothing
        , right
        , requires
        , ensures
        , attributes = Default.def
        }

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
