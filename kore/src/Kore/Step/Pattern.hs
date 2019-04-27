{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Representation of program configurations as conditional patterns.
-}
module Kore.Step.Pattern
    ( Pattern
    , fromPredicateSubstitution
    , toPredicate
    , Kore.Step.Pattern.allVariables
    , bottom
    , bottomOf
    , isBottom
    , isTop
    , Kore.Step.Pattern.mapVariables
    , substitutionToPredicate
    , toMLPattern
    , toStepPattern
    , top
    , topOf
    , fromTermLike
    , Kore.Step.Pattern.freeVariables
    -- * Re-exports
    , Conditional (..)
    , PredicateSubstitution
    , module Kore.Step.TermLike
    ) where

import qualified Data.Functor.Foldable as Recursive
import           Data.Monoid
                 ( (<>) )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           GHC.Stack
                 ( HasCallStack )

import           Kore.Annotation.Valid
import qualified Kore.AST.Common as Common.Pattern
                 ( Pattern (..) )
import           Kore.AST.Valid
import           Kore.Predicate.Predicate as Predicate
import           Kore.Step.Conditional
                 ( Conditional (..) )
import qualified Kore.Step.Conditional as Conditional
import           Kore.Step.Representation.PredicateSubstitution
                 ( PredicateSubstitution )
import           Kore.Step.TermLike
                 ( CofreeF (..), Object, Sort, SortedVariable, TermLike,
                 Variable )
import qualified Kore.Step.TermLike as TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Free
                 ( pureAllVariables )

{- | The conjunction of a pattern, predicate, and substitution.

The form of @Pattern@ is intended to be a convenient representation of a
program configuration for Kore execution.

 -}
type Pattern level variable =
    Conditional level variable (TermLike variable)

fromPredicateSubstitution
    :: PredicateSubstitution Object variable
    -> Pattern Object variable
fromPredicateSubstitution = (<$) mkTop_

freeVariables
    :: Ord (variable Object)
    => Pattern Object variable
    -> Set (variable Object)
freeVariables = Conditional.freeVariables TermLike.freeVariables

{-|'mapVariables' transforms all variables, including the quantified ones,
in an Pattern.
-}
mapVariables
    :: Ord (variableTo Object)
    => (variableFrom Object -> variableTo Object)
    -> Pattern Object variableFrom
    -> Pattern Object variableTo
mapVariables
    variableMapper
    Conditional { term, predicate, substitution }
  =
    Conditional
        { term = TermLike.mapVariables variableMapper term
        , predicate = Predicate.mapVariables variableMapper predicate
        , substitution =
            Substitution.mapVariables variableMapper substitution
        }

{-|'allVariables' extracts all variables, including the quantified ones,
from an Pattern.
-}
allVariables
    :: (Ord (variable Object), Unparse (variable Object))
    => Pattern Object variable
    -> Set.Set (variable Object)
allVariables
    Conditional { term, predicate, substitution }
  =
    pureAllVariables term
    <> Predicate.allVariables predicate
    <> allSubstitutionVars (Substitution.unwrap substitution)
  where
    allSubstitutionVars sub =
        foldl
            (\ x y -> x <> Set.singleton (fst y))
            Set.empty
            sub
        <> foldl
            (\ x y -> x <> pureAllVariables (snd y))
            Set.empty
            sub

{- | Convert an 'Pattern' to an ordinary 'TermLike'.

Conversion relies on the interpretation of 'Pattern' as a conjunction of
patterns. Conversion erases the distinction between terms, predicates, and
substitutions; this function should be used with care where that distinction is
important.

 -}
toStepPattern
    ::  forall variable.
        ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , HasCallStack
        )
    => Pattern Object variable -> TermLike variable
toStepPattern
    Conditional { term, predicate, substitution }
  =
    simpleAnd
        (simpleAnd term predicate)
        (substitutionToPredicate substitution)
  where
    -- TODO: Most likely I defined this somewhere.
    simpleAnd
        :: TermLike variable
        -> Predicate variable
        -> TermLike variable
    simpleAnd pattern'@(Recursive.project -> valid :< projected) =
        \case
            PredicateTrue -> pattern'
            PredicateFalse -> mkBottom patternSort
            predicate' ->
                case projected of
                    Common.Pattern.TopPattern _ ->
                        Predicate.fromPredicate patternSort predicate'
                    Common.Pattern.BottomPattern _ -> pattern'
                    _ -> mkAnd pattern' (Predicate.fromPredicate patternSort predicate')
      where
        Valid { patternSort } = valid

toMLPattern
    ::  forall variable.
        ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , HasCallStack
        )
    => Pattern Object variable -> TermLike variable
toMLPattern = toStepPattern

{-|'bottom' is an expanded pattern that has a bottom condition and that
should become Bottom when transformed to a ML pattern.
-}
bottom :: Ord (variable Object) => Pattern Object variable
bottom =
    Conditional
        { term      = mkBottom_
        , predicate = makeFalsePredicate
        , substitution = mempty
        }

{- | An 'Pattern' where the 'term' is 'Bottom' of the given 'Sort'.

The 'predicate' is set to 'makeFalsePredicate'.

 -}
bottomOf :: Ord (variable Object) => Sort Object -> Pattern Object variable
bottomOf resultSort =
    Conditional
        { term      = mkBottom resultSort
        , predicate = makeFalsePredicate
        , substitution = mempty
        }

{-|'top' is an expanded pattern that has a top condition and that
should become Top when transformed to a ML pattern.
-}
top :: Ord (variable Object) => Pattern Object variable
top =
    Conditional
        { term      = mkTop_
        , predicate = makeTruePredicate
        , substitution = mempty
        }

{- | An 'Pattern' where the 'term' is 'Top' of the given 'Sort'.
 -}
topOf :: Ord (variable Object) => Sort Object -> Pattern Object variable
topOf resultSort =
    Conditional
        { term      = mkTop resultSort
        , predicate = makeTruePredicate
        , substitution = mempty
        }

{- | Construct an 'Pattern' from a 'TermLike'.

The resulting @Pattern@ has a true predicate and an empty
substitution, unless it is trivially 'Bottom'.

See also: 'makeTruePredicate', 'pure'

 -}
fromTermLike
    :: Ord (variable Object)
    => TermLike variable
    -> Pattern Object variable
fromTermLike term
  | isBottom term = bottom
  | otherwise =
    Conditional
        { term
        , predicate = makeTruePredicate
        , substitution = mempty
        }

toPredicate
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable
    -> Predicate variable
toPredicate = Conditional.toPredicate
