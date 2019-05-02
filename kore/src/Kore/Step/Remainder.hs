{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Step.Remainder
    ( remainder
    , existentiallyQuantifyTarget
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Data.Foldable as Foldable
import qualified Data.Set as Set

import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Conditional
                 ( Conditional (Conditional) )
import           Kore.Step.Predicate
                 ( Predicate )
import           Kore.Step.Representation.MultiAnd
                 ( MultiAnd )
import qualified Kore.Step.Representation.MultiAnd as MultiAnd
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Target
                 ( Target )
import qualified Kore.Variables.Target as Target

{- | Negate the disjunction of unification solutions to form the /remainder/.

The /remainder/ is the parts of the initial configuration that is not matched
by any applied rule.

 -}
remainder
    ::  ( Ord     variable
        , Show    variable
        , Unparse variable
        , SortedVariable variable
        )
    => MultiOr (Predicate (Target variable))
    -> Syntax.Predicate variable
remainder results =
    mkMultiAndPredicate $ mkNotExists conditions
  where
    conditions = mkMultiAndPredicate . unificationConditions <$> results
    mkNotExists = mkNotMultiOr . fmap existentiallyQuantifyTarget

-- | Existentially-quantify target (axiom) variables in the 'Predicate'.
existentiallyQuantifyTarget
    ::  ( Ord     variable
        , Show    variable
        , Unparse variable
        , SortedVariable variable
        )
    => Syntax.Predicate (Target variable)
    -> Syntax.Predicate variable
existentiallyQuantifyTarget predicate =
    Syntax.Predicate.mapVariables Target.unwrapVariable
    $ Syntax.Predicate.makeMultipleExists freeTargetVariables predicate
  where
    freeTargetVariables =
        Set.filter Target.isTarget
        $ Syntax.Predicate.freeVariables predicate

{- | Negate a disjunction of many terms.

@
  ¬ (φ₁ ∨ φ₂ ∨ ...) = ¬φ₁ ∧ ¬φ₂ ∧ ...
@

 -}
mkNotMultiOr
    ::  ( Ord     variable
        , Show    variable
        , Unparse variable
        , SortedVariable variable
        )
    => MultiOr  (Syntax.Predicate variable)
    -> MultiAnd (Syntax.Predicate variable)
mkNotMultiOr =
    MultiAnd.make
    . map Syntax.Predicate.makeNotPredicate
    . Foldable.toList

mkMultiAndPredicate
    ::  ( Ord     variable
        , Show    variable
        , Unparse variable
        , SortedVariable variable
        )
    => MultiAnd (Syntax.Predicate variable)
    ->           Syntax.Predicate variable
mkMultiAndPredicate =
    Syntax.Predicate.makeMultipleAndPredicate . Foldable.toList

{- | Represent the unification solution as a conjunction of predicates.
 -}
unificationConditions
    ::  ( Ord     variable
        , Show    variable
        , Unparse variable
        , SortedVariable variable
        )
    => Predicate (Target variable)
    -- ^ Unification solution
    -> MultiAnd (Syntax.Predicate (Target variable))
unificationConditions Conditional { predicate, substitution } =
    pure predicate <|> substitutionConditions substitution'
  where
    substitution' = Substitution.filter Target.isNonTarget substitution

substitutionConditions
    ::  ( Ord     variable
        , Show    variable
        , Unparse variable
        , SortedVariable variable
        )
    => Substitution variable
    -> MultiAnd (Syntax.Predicate variable)
substitutionConditions subst =
    MultiAnd.make (substitutionCoverageWorker <$> Substitution.unwrap subst)
  where
    substitutionCoverageWorker (x, t) =
        Syntax.Predicate.makeEqualsPredicate (mkVar x) t
