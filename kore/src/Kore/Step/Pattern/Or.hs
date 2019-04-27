{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Pattern.Or
    ( Conditional
    , Pattern
    , PredicateSubstitution
    , isFalse
    , isTrue
    , makeFromSinglePurePattern
    , toExpandedPattern
    , toTermLike
    , toPredicate
    ) where

import Data.List
       ( foldl' )

import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Step.Conditional as Conditional
import qualified Kore.Step.Pattern as Pattern
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import qualified Kore.Step.Representation.PredicateSubstitution as PredicateSubstitution
import           Kore.Step.TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser

{-| The disjunction of 'Conditional'.
-}
type Conditional level variable term =
    MultiOr (Conditional.Conditional level variable term)

{-| The disjunction of 'Pattern'.
-}
type Pattern level variable = MultiOr (Pattern.Pattern level variable)

{-| The disjunction of 'PredicateSubstitution.PredicateSubstitution'.
-}
type PredicateSubstitution level variable =
    MultiOr (PredicateSubstitution.PredicateSubstitution level variable)

{-| The disjunction of 'Predicate'.
-}
type Predicate variable = MultiOr (Predicate.Predicate variable)

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

{-| 'toExpandedPattern' transforms an 'Pattern' into
an 'Pattern.Pattern'.
-}
toExpandedPattern
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable -> Pattern.Pattern Object variable
toExpandedPattern multiOr
  =
    case MultiOr.extractPatterns multiOr of
        [] -> Pattern.bottom
        [patt] -> patt
        patt : patts ->
            Conditional.Conditional
                { term =
                    foldl'
                        (\x y -> mkOr x (Pattern.toMLPattern y))
                        (Pattern.toMLPattern patt)
                        patts
                , predicate = Predicate.makeTruePredicate
                , substitution = mempty
                }

{-| Transforms a 'Pattern' into a 'TermLike'.
-}
toTermLike
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable -> TermLike variable
toTermLike multiOr =
    case MultiOr.extractPatterns multiOr of
        [] -> mkBottom_
        [patt] -> Pattern.toMLPattern patt
        patt : patts ->
            foldl'
                (\x y -> mkOr x (Pattern.toMLPattern y))
                (Pattern.toMLPattern patt)
                patts

{-| Transforms an 'Predicate' into a 'Predicate.Predicate'. -}
toPredicate
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Predicate variable -> Predicate.Predicate variable
toPredicate multiOr =
    Predicate.makeMultipleOrPredicate (MultiOr.extractPatterns multiOr)
