{-|
Module      : Data.Kore.Algorithm.SetWithInsertionOrder
Description : Set from which one can extract the list of elements in the
              insertion order. Does not support all set operations.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Algorithm.SetWithInsertionOrder
    (SetWithInsertionOrder, empty, insert, member, insertionOrder)
  where

import qualified Data.Set                    as Set

import           Data.Kore.HaskellExtensions (ReversedList, emptyReversedList,
                                              reversedAdd, reversedToList)

{--| 'SetWithInsertionOrder' represents a set from which elements can be
retrieved as a list, in the order of their insertion.
--}
data SetWithInsertionOrder a = SetWithInsertionOrder
    { setWithOriginalOrderSet   :: !(Set.Set a)
    , setWithOriginalOrderOrder :: !(ReversedList a)
    }

{--| 'empty' builds an empty 'SetWithInsertionOrder'.
--}
empty :: Ord a => SetWithInsertionOrder a
empty =
    SetWithInsertionOrder
        { setWithOriginalOrderSet = Set.empty
        , setWithOriginalOrderOrder = emptyReversedList
        }

{--| 'insert' adds an element to a 'SetWithInsertionOrder'.

If the element already exists in the set then the set does not change.
--}
insert :: Ord a => a -> SetWithInsertionOrder a -> SetWithInsertionOrder a
insert
    element
    s @ SetWithInsertionOrder
        { setWithOriginalOrderSet = set'
        , setWithOriginalOrderOrder = order
        }
  | Set.member element set' = s
  | otherwise =
        SetWithInsertionOrder
            { setWithOriginalOrderSet = Set.insert element set'
            , setWithOriginalOrderOrder = element `reversedAdd` order
            }


{--| 'member' checks whether an element belongs to a 'SetWithInsertionOrder'.
--}
member :: Ord a => a -> SetWithInsertionOrder a -> Bool
member
    element
    SetWithInsertionOrder { setWithOriginalOrderSet = set }
  =
    Set.member element set

{--| 'insertionOrder' retrieves the elements of a 'SetWithInsertionOrder' in
their insertion order.
--}
insertionOrder :: SetWithInsertionOrder a -> [a]
insertionOrder
    SetWithInsertionOrder { setWithOriginalOrderOrder = order }
  =
    reversedToList order
