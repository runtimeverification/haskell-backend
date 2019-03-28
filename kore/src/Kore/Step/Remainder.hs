{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Step.Remainder
    ( remainders
    , remainder
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Data.Foldable as Foldable

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Representation.MultiAnd
                 ( MultiAnd )
import qualified Kore.Step.Representation.MultiAnd as MultiAnd
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Representation.Predicated
                 ( Predicated (Predicated) )
import           Kore.Step.Representation.PredicateSubstitution
                 ( PredicateSubstitution )
import           Kore.Unification.Substitution
                 ( Substitution )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Target
                 ( Target )
import qualified Kore.Variables.Target as Target

{- | Negate the disjunction of unification solutions to form the /remainders/.

The /remainders/ are the parts of the initial configuration that are not matched
by any applied rule.

@remainders@ returns a disjunction of predicates; use 'remainder' to construct a
single remainder predicate.

 -}
remainders
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiOr (PredicateSubstitution Object (Target variable))
    -> MultiOr (Predicate Object variable)
remainders =
    fmap unwrapRemainder
    . Foldable.foldr negateUnification1 top
  where
    top = pure Predicate.makeTruePredicate
    negateUnification1 unification negations =
        Predicate.makeAndPredicate
            <$> mkNotMultiAnd conditions
            <*> negations
      where
        conditions = unificationConditions unification

{- | Negate the disjunction of unification solutions to form the /remainder/.

The /remainder/ is the parts of the initial configuration that is not matched
by any applied rule.

@remainder@ returns a single predicate; use 'remainders' to construct a a
disjunction of remainder predicates.

 -}
remainder
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiOr (PredicateSubstitution Object (Target variable))
    -> Predicate Object variable
remainder results =
    unwrapRemainder
    $ mkMultiAndPredicate
    $ mkNotMultiOr conditions
  where
    conditions = mkMultiAndPredicate . unificationConditions <$> results

{- | Unwrap a remainder predicate.

 -}
unwrapRemainder
    :: (Ord (variable Object), Unparse (variable Object))
    => Predicate Object (Target variable)
    -> Predicate Object variable
unwrapRemainder remainder' =
    Predicate.mapVariables Target.unwrapVariable remainder'

mkNotMultiAnd
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiAnd (Predicate Object variable)
    -> MultiOr  (Predicate Object variable)
mkNotMultiAnd = MultiOr.make . map Predicate.makeNotPredicate . Foldable.toList

mkNotMultiOr
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiOr  (Predicate Object variable)
    -> MultiAnd (Predicate Object variable)
mkNotMultiOr = MultiAnd.make . map Predicate.makeNotPredicate . Foldable.toList

mkMultiAndPredicate
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => MultiAnd (Predicate Object variable)
    ->           Predicate Object variable
mkMultiAndPredicate = Predicate.makeMultipleAndPredicate . Foldable.toList

{- | Represent the unification solution as a conjunction of predicates.
 -}
unificationConditions
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => PredicateSubstitution Object (Target variable)
    -- ^ Unification solution
    -> MultiAnd (Predicate Object (Target variable))
unificationConditions Predicated { predicate, substitution } =
    pure predicate <|> substitutionConditions substitution'
  where
    substitution' = Substitution.filter Target.isNonTarget substitution

substitutionConditions
    ::  ( Ord     (variable Object)
        , Show    (variable Object)
        , Unparse (variable Object)
        , SortedVariable variable
        )
    => Substitution Object variable
    -> MultiAnd (Predicate Object variable)
substitutionConditions subst =
    MultiAnd.make (substitutionCoverageWorker <$> Substitution.unwrap subst)
  where
    substitutionCoverageWorker (x, t) =
        Predicate.makeEqualsPredicate (mkVar x) t
