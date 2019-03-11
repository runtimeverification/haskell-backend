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
    , toPredicate
    ) where

import Data.List
       ( foldl' )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( Predicate, makeMultipleOrPredicate, makeTruePredicate )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser

type OrOfPredicated level variable term =
    MultiOr (Predicated level variable term)

{-| 'OrOfExpandedPattern' is a 'MultiOr' of 'ExpandedPatterns', which is the
most common case.
-}
type OrOfExpandedPattern level variable
    = OrOfPredicated level variable (StepPattern level variable)

{-| 'OrOfPredicateSubstitution' is a 'MultiOr' of 'PredicateSubstitution'.
-}
type OrOfPredicateSubstitution level variable
    = OrOfPredicated level variable ()

{-| 'OrOfPredicate' is a 'MultiOr' of 'Predicate'.
-}
type OrOfPredicate level variable =
    MultiOr (Predicate level variable)

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
'StepPatterns'.
-}
makeFromSinglePurePattern
    :: (MetaOrObject level, Ord (variable level))
    => StepPattern level variable
    -> OrOfExpandedPattern level variable
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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => OrOfExpandedPattern level variable -> ExpandedPattern level variable
toExpandedPattern multiOr
  =
    case MultiOr.extractPatterns multiOr of
        [] -> ExpandedPattern.bottom
        [patt] -> patt
        patt : patts -> Predicated
            { term = foldl'
                (\x y -> mkOr x (ExpandedPattern.toMLPattern y))
                (ExpandedPattern.toMLPattern patt)
                patts
            , predicate = makeTruePredicate
            , substitution = mempty
            }

{-| Transforms an 'OrOfPredicate' into a 'Predicate'. -}
toPredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => OrOfPredicate level variable -> Predicate level variable
toPredicate multiOr =
    makeMultipleOrPredicate (MultiOr.extractPatterns multiOr)
