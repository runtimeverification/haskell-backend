{-|
Module      : Kore.Step.Representation.OrOfExpandedPattern
Description : Data structures and functions for manipulating
              OrOfExpandedPatterns, which occur naturally during
              pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Representation.OrOfExpandedPattern
    ( CommonOrOfExpandedPattern
    , CommonOrOfPredicateSubstitution
    , OrOfExpandedPattern
    , OrOfPredicateSubstitution
    , isFalse
    , isTrue
    , makeFromSinglePurePattern
    , toExpandedPattern
    , toStepPattern
    , toPredicate
    ) where

import Data.List
       ( foldl' )

import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( Predicate, makeMultipleOrPredicate, makeTruePredicate )
import           Kore.Step.Pattern
                 ( Conditional (..), Object, Pattern, SortedVariable,
                 Variable )
import qualified Kore.Step.Pattern as ExpandedPattern
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.TermLike
                 ( TermLike )
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser

type OrOfConditional level variable term =
    MultiOr (Conditional level variable term)

{-| 'OrOfExpandedPattern' is a 'MultiOr' of 'ExpandedPatterns', which is the
most common case.
-}
type OrOfExpandedPattern level variable
    = OrOfConditional level variable (TermLike variable)

{-| 'OrOfPredicateSubstitution' is a 'MultiOr' of 'PredicateSubstitution'.
-}
type OrOfPredicateSubstitution level variable
    = OrOfConditional level variable ()

{-| 'OrOfPredicate' is a 'MultiOr' of 'Predicate'.
-}
type OrOfPredicate variable =
    MultiOr (Predicate variable)

{-| 'CommonOrOfExpandedPattern' particularizes 'OrOfExpandedPattern' to
'Variable', following the same convention as the other Common* types.
-}
type CommonOrOfExpandedPattern level = OrOfExpandedPattern level Variable

{-| 'CommonOrOfOrOfPredicateSubstitution' particularizes
'OrOfPredicateSubstitution' to 'Variable', following the same convention
as the other Common* types.
-}
type CommonOrOfPredicateSubstitution level =
    OrOfPredicateSubstitution level Variable

{-| Constructs a normalized 'OrOfExpandedPattern' from
'TermLikes'.
-}
makeFromSinglePurePattern
    :: Ord (variable Object)
    => TermLike variable
    -> OrOfExpandedPattern Object variable
makeFromSinglePurePattern patt =
    MultiOr.make [ ExpandedPattern.fromPurePattern patt ]

{-| 'isFalse' checks if the 'Or' is composed only of bottom items.
-}
isFalse
    :: (Ord term, TopBottom term)
    => MultiOr term
    -> Bool
isFalse patt =
    isBottom (MultiOr.make (MultiOr.extractPatterns patt))

{-| 'isTrue' checks if the 'Or' has a single top pattern.
-}
isTrue
    :: (Ord term, TopBottom term)
    => MultiOr term
    -> Bool
isTrue = isTop

{-| 'toExpandedPattern' transforms an 'OrOfExpandedPattern' into
an 'ExpandedPattern'.
-}
toExpandedPattern
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => OrOfExpandedPattern Object variable -> Pattern Object variable
toExpandedPattern multiOr
  =
    case MultiOr.extractPatterns multiOr of
        [] -> ExpandedPattern.bottom
        [patt] -> patt
        patt : patts -> Conditional
            { term = foldl'
                (\x y -> mkOr x (ExpandedPattern.toMLPattern y))
                (ExpandedPattern.toMLPattern patt)
                patts
            , predicate = makeTruePredicate
            , substitution = mempty
            }

{-| Transforms an 'OrOfExpandedPattern' into a 'TermLike'.
-}
toStepPattern
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => OrOfExpandedPattern Object variable -> TermLike variable
toStepPattern multiOr =
    case MultiOr.extractPatterns multiOr of
        [] -> mkBottom_
        [patt] -> ExpandedPattern.toMLPattern patt
        patt : patts ->
            foldl'
                (\x y -> mkOr x (ExpandedPattern.toMLPattern y))
                (ExpandedPattern.toMLPattern patt)
                patts

{-| Transforms an 'OrOfPredicate' into a 'Predicate'. -}
toPredicate
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => OrOfPredicate variable -> Predicate variable
toPredicate multiOr =
    makeMultipleOrPredicate (MultiOr.extractPatterns multiOr)
