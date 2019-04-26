{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Or
    ( Pattern
    , PredicateSubstitution
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
import qualified Kore.Step.Conditional as Conditional
import qualified Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.TermLike
                 ( TermLike )
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser

type Conditional level variable term =
    MultiOr (Conditional.Conditional level variable term)

{-| 'Pattern' is a 'MultiOr' of 'Patterns', which is the
most common case.
-}
type Pattern level variable = MultiOr (Pattern.Pattern level variable)

{-| 'PredicateSubstitution' is a 'MultiOr' of 'PredicateSubstitution.PredicateSubstitution'.
-}
type PredicateSubstitution level variable =
    MultiOr (PredicateSubstitution.PredicateSubstitution level variable)

{-| 'OrOfPredicate' is a 'MultiOr' of 'Predicate'.
-}
type Predicate variable = MultiOr (Predicate variable)

{-| Constructs a normalized 'Pattern' from
'TermLike's.
-}
makeFromSinglePurePattern
    :: Ord (variable Object)
    => TermLike variable
    -> Pattern Object variable
makeFromSinglePurePattern patt =
    MultiOr.make [ Pattern.fromPurePattern patt ]

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
