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

import           Kore.AST.MetaOrObject
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
type OrPredicate level variable = MultiOr (Predicate level variable)

{- | A "disjunction" of one 'Predicate'.
 -}
fromPredicate
    :: Ord (variable Object)
    => Predicate Object variable
    -> OrPredicate Object variable
fromPredicate = MultiOr.singleton

{- | Disjoin a collection of predicates.
 -}
fromPredicates
    :: (Foldable f, Ord (variable Object))
    => f (Predicate Object variable)
    -> OrPredicate Object variable
fromPredicates = MultiOr.make . Foldable.toList

{-| 'isFalse' checks if the 'OrPredicate' is composed only of bottom items.
-}
isFalse :: Ord (variable Object) => OrPredicate Object variable -> Bool
isFalse = isBottom

{-| 'isTrue' checks if the 'OrPredicate' has a single top pattern.
-}
isTrue :: Ord (variable Object) => OrPredicate Object variable -> Bool
isTrue = isTop

{-| Transforms an 'Predicate' into a 'Predicate.Predicate'. -}
toPredicate
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => MultiOr (Syntax.Predicate variable) -> Syntax.Predicate variable
toPredicate multiOr =
    Syntax.Predicate.makeMultipleOrPredicate (MultiOr.extractPatterns multiOr)
