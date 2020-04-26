{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Step.Remainder
    ( remainder, remainder'
    , existentiallyQuantifyRuleVariables
    , ceilChildOfApplicationOrTop
    ) where

import Prelude.Kore

import qualified Data.Foldable as Foldable

import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.Substitution
    ( pattern Assignment
    , Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
import qualified Kore.Step.Simplification.AndPredicates as AndPredicates
import qualified Kore.Step.Simplification.Ceil as Ceil
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify (..)
    )
import Kore.Variables.UnifiedVariable
    ( foldMapVariable
    )

{- | Negate the disjunction of unification solutions to form the /remainder/.

The /remainder/ is the parts of the initial configuration that is not matched
by any applied rule.

The resulting predicate has the 'Target' variables unwrapped.

See also: 'remainder\''

 -}
remainder
    :: MultiOr (Condition RewritingVariable)
    -> Predicate Variable
remainder =
    Predicate.mapVariables getElementRewritingVariable getSetRewritingVariable
    . remainder'

{- | Negate the disjunction of unification solutions to form the /remainder/.

The /remainder/ is the parts of the initial configuration that is not matched
by any applied rule.

 -}
remainder'
    :: MultiOr (Condition RewritingVariable)
    -> Predicate RewritingVariable
remainder' results =
    mkMultiAndPredicate $ mkNotExists conditions
  where
    conditions = mkMultiAndPredicate . unificationConditions <$> results
    mkNotExists = mkNotMultiOr . fmap existentiallyQuantifyRuleVariables

-- | Existentially-quantify target (axiom) variables in the 'Condition'.
existentiallyQuantifyRuleVariables
    :: Predicate RewritingVariable
    -> Predicate RewritingVariable
existentiallyQuantifyRuleVariables predicate =
    Predicate.makeMultipleExists freeRuleVariables predicate
  where
    freeRuleVariables =
        filter (isRuleVariable . getElementVariable)
        . Predicate.freeElementVariables
        $ predicate

{- | Negate a disjunction of many terms.

@
  ¬ (φ₁ ∨ φ₂ ∨ ...) = ¬φ₁ ∧ ¬φ₂ ∧ ...
@

 -}
mkNotMultiOr
    :: InternalVariable variable
    => MultiOr  (Predicate variable)
    -> MultiAnd (Predicate variable)
mkNotMultiOr =
    MultiAnd.make
    . map Predicate.makeNotPredicate
    . Foldable.toList

mkMultiAndPredicate
    :: InternalVariable variable
    => MultiAnd (Predicate variable)
    ->           Predicate variable
mkMultiAndPredicate =
    Predicate.makeMultipleAndPredicate . Foldable.toList

{- | Represent the unification solution as a conjunction of predicates.
 -}
unificationConditions
    :: Condition RewritingVariable
    -- ^ Unification solution
    -> MultiAnd (Predicate RewritingVariable)
unificationConditions Conditional { predicate, substitution } =
    pure predicate <|> substitutionConditions substitution'
  where
    substitution' =
        Substitution.filter
            (foldMapVariable isConfigVariable)
            substitution

substitutionConditions
    :: InternalVariable variable
    => Substitution variable
    -> MultiAnd (Predicate variable)
substitutionConditions subst =
    MultiAnd.make (substitutionCoverageWorker <$> Substitution.unwrap subst)
  where
    substitutionCoverageWorker (Assignment x t) =
        Predicate.makeEqualsPredicate_ (mkVar x) t

ceilChildOfApplicationOrTop
    :: forall variable m
    .  (InternalVariable variable, MonadSimplify m)
    => SideCondition variable
    -> TermLike variable
    -> m (Condition variable)
ceilChildOfApplicationOrTop sideCondition patt =
    case patt of
        App_ _ children -> do
            ceil <-
                traverse (Ceil.makeEvaluateTerm sideCondition) children
                >>= ( AndPredicates.simplifyEvaluatedMultiPredicate
                        sideCondition
                    . MultiAnd.make
                    )
            pure Conditional
                { term = ()
                , predicate =
                    OrCondition.toPredicate
                    . fmap Condition.toPredicate
                    $ ceil
                , substitution = mempty
                }
        _ -> pure Condition.top
