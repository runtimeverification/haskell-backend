{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}

module Kore.Strategies.OnePath.Actions
    ( derivePar
    , deriveSeq
    , getConfiguration
    , getDestination
    , isTriviallyValid
    , isTrusted
    , makeRuleFromPatterns
    , removeDestination
    , simplify
    ) where

import qualified Control.Monad.Trans as Monad.Trans
import Data.Coerce
    ( Coercible
    , coerce
    )
import qualified Data.Default as Default
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

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
import qualified Kore.Strategies.ProofState as Goal
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

isTrusted :: OnePathRule variable -> Bool
isTrusted =
    Attribute.Trusted.isTrusted
    . Attribute.Axiom.trusted
    . RulePattern.attributes
    . coerce

removeDestination
    ::  ( MonadSimplify m
        , SimplifierVariable variable
        , goal ~ OnePathRule variable
        )
    => goal
    -> Strategy.TransitionT rule m (OnePathRule variable)
removeDestination goal = do
    let destination = getDestination goal
        configuration = getConfiguration goal
        removal = removalPredicate destination configuration
        result = Conditional.andPredicate configuration removal
    pure $ makeRuleFromPatterns result destination

simplify
    ::  ( MonadSimplify m
        , SimplifierVariable variable
        , goal ~ OnePathRule variable
        )
    => goal
    -> Strategy.TransitionT rule m goal
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

isTriviallyValid :: OnePathRule variable -> Bool
isTriviallyValid = isBottom . RulePattern.left . coerce

-- | Apply 'Rule's to the goal in parallel.
derivePar
    :: forall goal m rule variable
    .   ( Coercible (RewriteRule variable) rule
        , Debug variable
        , FreshVariable variable
        , MonadSimplify m
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        , goal ~ OnePathRule variable
        )
    => [rule]
    -> goal
    -> Strategy.TransitionT rule m (Goal.ProofState goal)
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
                        (pure . Goal.Goal)
                        removeDestSimplifyRemainder
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
    :: forall goal m rule variable
    .   ( Coercible (RewriteRule variable) rule
        , Debug variable
        , FreshVariable variable
        , MonadSimplify m
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        , goal ~ OnePathRule variable
        )
    => [rule]
    -> goal
    -> Strategy.TransitionT rule m (Goal.ProofState goal)
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

removeDestSimplifyRemainder
    :: forall variable m rule
    .  MonadSimplify m
    => SortedVariable variable
    => Debug variable
    => Unparse variable
    => Show variable
    => FreshVariable variable
    => OnePathRule variable
    -> Strategy.TransitionT
        rule
        m
        (Goal.ProofState (OnePathRule variable))
removeDestSimplifyRemainder remainder = do
    result <- removeDestination remainder >>= simplify
    if isTriviallyValid result
       then pure Goal.Proven
       else pure . Goal.GoalRem $ result
