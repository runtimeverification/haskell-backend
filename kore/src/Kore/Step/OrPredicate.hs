{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.OrPredicate
    ( OrPredicate
    , fromPredicates
    , fromPredicate
    , isFalse
    , isTrue
    , toPredicate
    ) where

import qualified Data.Foldable as Foldable

import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Predicate
                 ( Predicate )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.TermLike
import           Kore.TopBottom
                 ( TopBottom (..) )
import           Kore.Unparser


{-| The disjunction of 'Predicate'.
-}
type OrPredicate variable = MultiOr (Predicate variable)

{- | A "disjunction" of one 'Predicate'.
 -}
fromPredicate
    :: Ord variable
    => Predicate variable
    -> OrPredicate variable
fromPredicate = MultiOr.singleton

{- | Disjoin a collection of predicates.
 -}
fromPredicates
    :: (Foldable f, Ord variable)
    => f (Predicate variable)
    -> OrPredicate variable
fromPredicates = MultiOr.make . Foldable.toList

{-| 'isFalse' checks if the 'OrPredicate' is composed only of bottom items.
-}
isFalse :: Ord variable => OrPredicate variable -> Bool
isFalse = isBottom

{-| 'isTrue' checks if the 'OrPredicate' has a single top pattern.
-}
isTrue :: Ord variable => OrPredicate variable -> Bool
isTrue = isTop

{-| Transforms an 'Predicate' into a 'Predicate.Predicate'. -}
toPredicate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => MultiOr (Syntax.Predicate variable) -> Syntax.Predicate variable
toPredicate multiOr =
    Syntax.Predicate.makeMultipleOrPredicate (MultiOr.extractPatterns multiOr)
