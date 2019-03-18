{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Representation of program configurations as conditional patterns.
-}
module Kore.Step.Representation.ExpandedPattern
    ( ExpandedPattern
    , CommonExpandedPattern
    , fromPredicateSubstitution
    , toPredicate
    , Kore.Step.Representation.ExpandedPattern.allVariables
    , bottom
    , bottomOf
    , isBottom
    , isTop
    , Kore.Step.Representation.ExpandedPattern.mapVariables
    , substitutionToPredicate
    , toMLPattern
    , top
    , topOf
    , Kore.Step.Representation.ExpandedPattern.fromPurePattern
    , Kore.Step.Representation.ExpandedPattern.freeVariables
    -- * Re-exports
    , Predicated (..)
    , PredicateSubstitution
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
import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate as Predicate
import           Kore.Step.Pattern
                 ( StepPattern )
import qualified Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.Predicated
                 ( Predicated (..) )
import qualified Kore.Step.Representation.Predicated as Predicated
import           Kore.Step.Representation.PredicateSubstitution
                 ( PredicateSubstitution )
import           Kore.TopBottom
                 ( TopBottom (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unparser
import           Kore.Variables.Free
                 ( pureAllVariables )

{- | The conjunction of a pattern, predicate, and substitution.

The form of @ExpandedPattern@ is intended to be a convenient representation of a
program configuration for Kore execution.

 -}
type ExpandedPattern level variable =
    Predicated level variable (StepPattern level variable)

{- | 'CommonExpandedPattern' instantiates 'ExpandedPattern' at 'Variable'.
-}
type CommonExpandedPattern level = ExpandedPattern level Variable

fromPredicateSubstitution
    :: MetaOrObject level
    => PredicateSubstitution level variable
    -> ExpandedPattern level variable
fromPredicateSubstitution = (<$) mkTop_

freeVariables
    :: ( MetaOrObject level
       , Ord (variable level)
       , Show (variable level)
       , Unparse (variable level)
       , SortedVariable variable
       )
    => ExpandedPattern level variable
    -> Set (variable level)
freeVariables = Predicated.freeVariables Pattern.freeVariables

{-|'mapVariables' transforms all variables, including the quantified ones,
in an ExpandedPattern.
-}
mapVariables
    :: Ord (variableTo level)
    => (variableFrom level -> variableTo level)
    -> ExpandedPattern level variableFrom
    -> ExpandedPattern level variableTo
mapVariables
    variableMapper
    Predicated { term, predicate, substitution }
  =
    Predicated
        { term = Pattern.mapVariables variableMapper term
        , predicate = Predicate.mapVariables variableMapper predicate
        , substitution =
            Substitution.mapVariables variableMapper substitution
        }

{-|'allVariables' extracts all variables, including the quantified ones,
from an ExpandedPattern.
-}
allVariables
    :: (Ord (variable level), Unparse (variable level))
    => ExpandedPattern level variable
    -> Set.Set (variable level)
allVariables
    Predicated { term, predicate, substitution }
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

{-|'toMLPattern' converts an ExpandedPattern to a StepPattern.
-}
toMLPattern
    ::  forall level variable.
        ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , HasCallStack
        )
    => ExpandedPattern level variable -> StepPattern level variable
toMLPattern
    Predicated { term, predicate, substitution }
  =
    simpleAnd
        (simpleAnd term predicate)
        (substitutionToPredicate substitution)
  where
    -- TODO: Most likely I defined this somewhere.
    simpleAnd
        :: StepPattern level variable
        -> Predicate level variable
        -> StepPattern level variable
    simpleAnd pattern'@(Recursive.project -> valid :< projected) =
        \case
            PredicateTrue -> pattern'
            PredicateFalse -> mkBottom patternSort
            predicate' ->
                case projected of
                    TopPattern _ ->
                        Predicate.fromPredicate patternSort predicate'
                    BottomPattern _ -> pattern'
                    _ -> mkAnd pattern' (Predicate.fromPredicate patternSort predicate')
      where
        Valid { patternSort } = valid

{-|'bottom' is an expanded pattern that has a bottom condition and that
should become Bottom when transformed to a ML pattern.
-}
bottom :: MetaOrObject level => ExpandedPattern level variable
bottom =
    Predicated
        { term      = mkBottom_
        , predicate = makeFalsePredicate
        , substitution = mempty
        }

{- | An 'ExpandedPattern' where the 'term' is 'Bottom' of the given 'Sort'.

The 'predicate' is set to 'makeFalsePredicate'.

 -}
bottomOf :: MetaOrObject level => Sort level -> ExpandedPattern level variable
bottomOf resultSort =
    Predicated
        { term      = mkBottom resultSort
        , predicate = makeFalsePredicate
        , substitution = mempty
        }

{-|'top' is an expanded pattern that has a top condition and that
should become Top when transformed to a ML pattern.
-}
top :: MetaOrObject level => ExpandedPattern level variable
top =
    Predicated
        { term      = mkTop_
        , predicate = makeTruePredicate
        , substitution = mempty
        }

{- | An 'ExpandedPattern' where the 'term' is 'Top' of the given 'Sort'.
 -}
topOf :: MetaOrObject level => Sort level -> ExpandedPattern level variable
topOf resultSort =
    Predicated
        { term      = mkTop resultSort
        , predicate = makeTruePredicate
        , substitution = mempty
        }

{- | Construct an 'ExpandedPattern' from a 'StepPattern'.

  The resulting @ExpandedPattern@ has a true predicate and an empty
  substitution.

  See also: 'makeTruePredicate', 'pure'

 -}
fromPurePattern
    :: MetaOrObject level
    => StepPattern level variable
    -> ExpandedPattern level variable
fromPurePattern term@(Recursive.project -> _ :< projected) =
    case projected of
        BottomPattern _ -> bottom
        _ ->
            Predicated
                { term
                , predicate = makeTruePredicate
                , substitution = mempty
                }

toPredicate
    :: ( MetaOrObject level
       , SortedVariable variable
       , Ord (variable level)
       , Show (variable level)
       , Unparse (variable level)
       )
    => ExpandedPattern level variable
    -> Predicate level variable
toPredicate = Predicated.toPredicate
