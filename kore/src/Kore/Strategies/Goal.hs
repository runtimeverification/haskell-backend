{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Strategies.Goal where

import Control.Applicative
    ( Alternative (..)
    )
import qualified Data.Foldable as Foldable
import Data.Maybe
    ( mapMaybe
    )
import qualified Generics.SOP as SOP
import GHC.Generics as GHC

import qualified Control.Monad.Trans as Monad.Trans
import Data.Coerce
    ( Coercible
    , coerce
    )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty
import Kore.Debug
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Step.Rule
    ( OnePathRule (..)
    , RewriteRule (..)
    )
import Kore.Step.Simplification.Data
    ( MonadSimplify
    , SimplifierVariable
    )
import Kore.Step.Strategy
    ( Strategy
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Strategies.ProofState hiding
    ( Prim
    , ProofState
    )
import qualified Kore.Strategies.ProofState as ProofState
import Kore.Unparser
    ( Unparse
    )

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Pattern.FreeVariables as Attribute.FreeVariables
import qualified Kore.Attribute.Trusted as Attribute.Trusted
import Kore.Debug
    ( Debug
    )
import qualified Kore.Internal.Conditional as Conditional
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
import qualified Kore.Step.Result as Result
import Kore.Step.Rule
    ( OnePathRule (OnePathRule)
    , RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
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
import qualified Kore.Step.Strategy as Strategy
import Kore.Syntax.Variable
    ( SortedVariable
    )
import Kore.TopBottom
    ( isBottom
    )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser
    ( Unparse
    , unparse
    )
import Kore.Variables.Fresh
    ( FreshVariable
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
        :: MonadSimplify m
        => Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)

    strategy
        :: [goal]
        -> [Rule goal]
        -> [Strategy (Prim goal)]

instance (SimplifierVariable variable) => Goal (OnePathRule variable) where

    newtype Rule (OnePathRule variable) =
        OnePathRewriteRule { unRule :: RewriteRule variable }
        deriving (GHC.Generic, Show, Unparse)

    type Prim (OnePathRule variable) =
        ProofState.Prim (Rule (OnePathRule variable))

    type ProofState (OnePathRule variable) a =
        ProofState.ProofState a

    transitionRule = transitionRule0

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

transitionRule0
    :: forall m goal variable
    .  MonadSimplify m
    => Goal goal
    => SimplifierVariable variable
    => Coercible goal (RulePattern variable)
    => Coercible (RulePattern variable) goal
    => Coercible (Rule goal) (RulePattern variable)
    => Coercible (RulePattern variable) (Rule goal)
    => ProofState goal goal ~ ProofState.ProofState goal
    => Prim goal ~ ProofState.Prim (Rule goal)
    => Prim goal
    -> ProofState goal goal
    -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
transitionRule0 = transitionRuleWorker
  where
    transitionRuleWorker
        :: Prim goal
        -> ProofState goal goal
        -> Strategy.TransitionT (Rule goal) m (ProofState goal goal)
    transitionRuleWorker CheckProven Proven = empty
    transitionRuleWorker CheckGoalRemainder (GoalRemainder _) = empty

    transitionRuleWorker ResetGoalRewritten (GoalRewritten goal) =
        return (Goal goal)

    transitionRuleWorker Simplify (Goal g) =
        Goal <$> simplify g
    transitionRuleWorker Simplify (GoalRemainder g) =
        GoalRemainder <$> simplify g

    transitionRuleWorker RemoveDestination (Goal g) =
        Goal <$> removeDestination g
    transitionRuleWorker RemoveDestination (GoalRemainder g) =
        GoalRemainder <$> removeDestination g

    transitionRuleWorker TriviallyValid (Goal g)
      | isTriviallyValid g = return Proven
    transitionRuleWorker TriviallyValid (GoalRemainder g)
      | isTriviallyValid g = return Proven
    transitionRuleWorker TriviallyValid (GoalRewritten g)
      | isTriviallyValid g = return Proven

    transitionRuleWorker (DerivePar rules) (Goal g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        derivePar rules g
    transitionRuleWorker (DerivePar rules) (GoalRemainder g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        derivePar rules g

    transitionRuleWorker (DeriveSeq rules) (Goal g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        deriveSeq rules g
    transitionRuleWorker (DeriveSeq rules) (GoalRemainder g) =
        -- TODO (virgil): Wrap the results in GoalRemainder/GoalRewritten here.
        deriveSeq rules g

    transitionRuleWorker _ state = return state

allPathStrategy
    :: [rule]
    -- ^ Claims
    -> [rule]
    -- ^ Axioms
    -> [Strategy (ProofState.Prim rule)]
allPathStrategy claims axioms =
    firstStep : repeat nextStep
  where
    firstStep =
        (Strategy.sequence . map Strategy.apply)
            [ CheckProven
            , CheckGoalRemainder
            , RemoveDestination
            , TriviallyValid
            , DerivePar axioms
            , RemoveDestination
            , Simplify
            , TriviallyValid
            , ResetGoalRewritten
            , TriviallyValid
            ]
    nextStep =
        (Strategy.sequence . map Strategy.apply)
            [ CheckProven
            , CheckGoalRemainder
            , RemoveDestination
            , TriviallyValid
            , DeriveSeq claims
            , RemoveDestination
            , Simplify
            , TriviallyValid
            , DerivePar axioms
            , RemoveDestination
            , Simplify
            , TriviallyValid
            , ResetGoalRewritten
            , TriviallyValid
            ]

-- TODO(Ana): make less general
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
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , ResetGoalRewritten
        , Simplify
        , TriviallyValid
        ]

-- TODO(Ana): make less general
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
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , DeriveSeq axioms
        , RemoveDestination
        , Simplify
        , TriviallyValid
        , ResetGoalRewritten
        , Simplify
        , TriviallyValid
        ]

instance SOP.Generic (Rule (OnePathRule variable))

instance SOP.HasDatatypeInfo (Rule (OnePathRule variable))

instance Debug variable => Debug (Rule (OnePathRule variable))

-- | Remove the destination of the goal.
removeDestination
    :: MonadSimplify m
    => Goal goal
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
    => Goal goal
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
    .  MonadSimplify m
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

-- | Apply 'Rule's to the goal in sequence.
deriveSeq
    :: forall m goal variable
    .  MonadSimplify m
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
