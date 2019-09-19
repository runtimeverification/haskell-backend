{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Step.Remainder
    ( remainder, remainder'
    , existentiallyQuantifyTarget
    , ceilChildOfApplicationOrTop
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import qualified Data.Foldable as Foldable

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
import qualified Kore.Internal.OrPredicate as OrPredicate
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Step.Simplification.AndPredicates as AndPredicates
import qualified Kore.Step.Simplification.Ceil as Ceil
import Kore.Step.Simplification.Simplify
    ( MonadSimplify (..)
    , SimplifierVariable
    )
import Kore.Unification.Substitution
    ( Substitution
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.Target
    ( Target
    )
import qualified Kore.Variables.Target as Target
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
    :: InternalVariable variable
    => MultiOr (Predicate (Target variable))
    -> Syntax.Predicate variable
remainder =
    Syntax.Predicate.mapVariables Target.unwrapVariable . remainder'

{- | Negate the disjunction of unification solutions to form the /remainder/.

The /remainder/ is the parts of the initial configuration that is not matched
by any applied rule.

 -}
remainder'
    :: InternalVariable variable
    => MultiOr (Predicate (Target variable))
    -> Syntax.Predicate (Target variable)
remainder' results =
    mkMultiAndPredicate $ mkNotExists conditions
  where
    conditions = mkMultiAndPredicate . unificationConditions <$> results
    mkNotExists = mkNotMultiOr . fmap existentiallyQuantifyTarget

-- | Existentially-quantify target (axiom) variables in the 'Predicate'.
existentiallyQuantifyTarget
    :: InternalVariable variable
    => Syntax.Predicate (Target variable)
    -> Syntax.Predicate (Target variable)
existentiallyQuantifyTarget predicate =
    Syntax.Predicate.makeMultipleExists freeTargetVariables predicate
  where
    freeTargetVariables =
        filter (Target.isTarget . getElementVariable)
        . Syntax.Predicate.freeElementVariables
        $ predicate

{- | Negate a disjunction of many terms.

@
  ¬ (φ₁ ∨ φ₂ ∨ ...) = ¬φ₁ ∧ ¬φ₂ ∧ ...
@

 -}
mkNotMultiOr
    :: InternalVariable variable
    => MultiOr  (Syntax.Predicate variable)
    -> MultiAnd (Syntax.Predicate variable)
mkNotMultiOr =
    MultiAnd.make
    . map Syntax.Predicate.makeNotPredicate
    . Foldable.toList

mkMultiAndPredicate
    :: InternalVariable variable
    => MultiAnd (Syntax.Predicate variable)
    ->           Syntax.Predicate variable
mkMultiAndPredicate =
    Syntax.Predicate.makeMultipleAndPredicate . Foldable.toList

{- | Represent the unification solution as a conjunction of predicates.
 -}
unificationConditions
    :: InternalVariable variable
    => Predicate (Target variable)
    -- ^ Unification solution
    -> MultiAnd (Syntax.Predicate (Target variable))
unificationConditions Conditional { predicate, substitution } =
    pure predicate <|> substitutionConditions substitution'
  where
    substitution' =
        Substitution.filter (foldMapVariable Target.isNonTarget)
            substitution

substitutionConditions
    :: InternalVariable variable
    => Substitution variable
    -> MultiAnd (Syntax.Predicate variable)
substitutionConditions subst =
    MultiAnd.make (substitutionCoverageWorker <$> Substitution.unwrap subst)
  where
    substitutionCoverageWorker (x, t) =
        Syntax.Predicate.makeEqualsPredicate (mkVar x) t

ceilChildOfApplicationOrTop
    :: forall variable m
    .  (SimplifierVariable variable, MonadSimplify m)
    => Predicate variable
    -> TermLike variable
    -> m (Predicate variable)
ceilChildOfApplicationOrTop predicate patt =
    case patt of
        App_ _ children -> do
            ceil <-
                traverse (Ceil.makeEvaluateTerm predicate) children
                >>= ( AndPredicates.simplifyEvaluatedMultiPredicate
                    . MultiAnd.make
                    )
            pure $ Conditional
                { term = ()
                , predicate =
                    OrPredicate.toPredicate
                    . fmap Predicate.toPredicate
                    $ ceil
                , substitution = mempty
                }
        _ -> pure Predicate.top
