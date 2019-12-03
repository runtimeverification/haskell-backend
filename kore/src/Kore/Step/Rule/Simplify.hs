{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Rule.Simplify
    ( SimplifyRuleLHS (..)
    ) where

import qualified Kore.Internal.Condition as Condition
    ( fromPredicate
    )
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
    ( withCondition
    )
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( make
    )
import qualified Kore.Internal.MultiOr as MultiOr
    ( extractPatterns
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeCeilPredicate_
    )
import Kore.Step.Rule
    ( AllPathRule (..)
    , OnePathRule (..)
    , ReachabilityRule (..)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    , applySubstitution
    )
import Kore.Step.Simplification.OrPattern
    ( simplifyConditionsWithSmt
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplifyAndRemoveTopExists
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )
import Kore.Syntax.Variable
    ( Variable
    )

-- | Simplifies the left-hand-side of a rule/claim
class SimplifyRuleLHS rule where
    simplifyRuleLhs
        :: forall simplifier
        .  MonadSimplify simplifier
        => rule
        -> simplifier (MultiAnd rule)

instance SimplifierVariable variable => SimplifyRuleLHS (RulePattern variable)
  where
    simplifyRuleLhs rule@(RulePattern _ _ _ _ _ _) = do
        let lhsPredicate =
                makeAndPredicate
                    requires
                    (makeCeilPredicate_ left)
            definedLhs =
                Conditional.withCondition left
                $ Condition.fromPredicate lhsPredicate
        simplifiedTerms <- Pattern.simplifyAndRemoveTopExists definedLhs
        fullySimplified <-
            simplifyConditionsWithSmt lhsPredicate simplifiedTerms
        let rules =
                map (setRuleLeft rule) (MultiOr.extractPatterns fullySimplified)
        return (MultiAnd.make rules)
      where
        RulePattern {left, requires} = rule

        setRuleLeft
            :: RulePattern variable
            -> Pattern variable
            -> RulePattern variable
        setRuleLeft
            rulePattern
            Conditional {term, predicate, substitution}
          =
            RulePattern.applySubstitution
                substitution
                rulePattern
                    { RulePattern.left = term
                    , RulePattern.requires = predicate
                    }

instance SimplifyRuleLHS (OnePathRule Variable) where
    simplifyRuleLhs = fmap (fmap OnePathRule) . simplifyRuleLhs . getOnePathRule

instance SimplifyRuleLHS (AllPathRule Variable) where
    simplifyRuleLhs = fmap (fmap AllPathRule) . simplifyRuleLhs . getAllPathRule

instance SimplifyRuleLHS (ReachabilityRule Variable) where
    simplifyRuleLhs (OnePath rule) =
        (fmap . fmap) OnePath $ simplifyRuleLhs rule
    simplifyRuleLhs (AllPath rule) =
        (fmap . fmap) AllPath $ simplifyRuleLhs rule
