{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Internal.OrCondition
    ( OrCondition
    , isSimplified
    , toConditions
    , fromConditions
    , fromCondition
    , gather
    , bottom
    , top
    , isFalse
    , isTrue
    , toPredicate
    ) where

import qualified Data.Foldable as Foldable

import Branch
    ( BranchT
    )
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.TermLike hiding
    ( isSimplified
    )
import Kore.TopBottom
    ( TopBottom (..)
    )


{-| The disjunction of 'Condition'.
-}
type OrCondition variable = MultiOr (Condition variable)

isSimplified :: SideCondition.Representation -> OrCondition variable -> Bool
isSimplified sideCondition = all (Condition.isSimplified sideCondition)

{- | A "disjunction" of one 'Condition'.
 -}
fromCondition
    :: Ord variable
    => Condition variable
    -> OrCondition variable
fromCondition = MultiOr.singleton

{- | Disjoin a collection of predicates.
 -}
fromConditions
    :: (Foldable f, Ord variable)
    => f (Condition variable)
    -> OrCondition variable
fromConditions = MultiOr.make . Foldable.toList

{- | @\\bottom@

@
'isFalse' bottom == True
@

 -}
bottom :: Ord variable => OrCondition variable
bottom = fromConditions []

{- | @\\top@

@
'isTrue' top == True
@

 -}
top :: InternalVariable variable => OrCondition variable
top = fromCondition Condition.top

{-| 'isFalse' checks if the 'OrCondition' is composed only of bottom items.
-}
isFalse :: OrCondition variable -> Bool
isFalse = isBottom

{-| 'isTrue' checks if the 'OrCondition' has a single top pattern.
-}
isTrue :: OrCondition variable -> Bool
isTrue = isTop

toConditions :: OrCondition variable -> [Condition variable]
toConditions = Foldable.toList

{-| Transforms an 'Predicate' into a 'Predicate.Predicate'. -}
toPredicate
    :: InternalVariable variable
    => MultiOr (Predicate variable) -> Predicate variable
toPredicate multiOr =
    Predicate.makeMultipleOrPredicate (MultiOr.extractPatterns multiOr)

gather
    :: (Ord variable, Monad m)
    => BranchT m (Condition variable) -> m (OrCondition variable)
gather = MultiOr.gather
