{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Internal.SideCondition
    ( SideCondition  -- Constructor not exported on purpose
    , addAssumedTrue
    , assumeTrueCondition
    , assumeTruePredicate
    , mapVariables
    , top
    , topTODO
    , toPredicate
    ) where

import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
    ( andCondition
    , fromPredicate
    , mapVariables
    , toPredicate
    , top
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )

newtype SideCondition variable =
    SideCondition
        { assumedTrue :: Condition variable }
    deriving (Eq, Show)

instance TopBottom (SideCondition variable) where
    isTop sideCondition@(SideCondition _) =
        isTop assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition
    isBottom sideCondition@(SideCondition _) =
        isBottom assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

instance InternalVariable variable
    => HasFreeVariables (SideCondition variable) variable
  where
    freeVariables sideCondition@(SideCondition _) =
        freeVariables assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

instance InternalVariable variable => Unparse (SideCondition variable) where
    unparse sideCondition@(SideCondition _) =
        unparse assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

    unparse2 sideCondition@(SideCondition _) =
        unparse2 assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

top :: InternalVariable variable => SideCondition variable
top = SideCondition
    { assumedTrue = Condition.top
    }

-- | A 'top' 'Condition' for refactoring which should eventually be removed.
topTODO :: InternalVariable variable => SideCondition variable
topTODO = top

addAssumedTrue
    :: InternalVariable variable
    => SideCondition variable
    -> Condition variable
    -> SideCondition variable
addAssumedTrue sideCondition@SideCondition {assumedTrue} newCondition =
    sideCondition
        { assumedTrue = assumedTrue `Condition.andCondition` newCondition }

assumeTrueCondition
    :: InternalVariable variable => Condition variable -> SideCondition variable
assumeTrueCondition condition =
    addAssumedTrue top condition

assumeTruePredicate
    :: InternalVariable variable => Predicate variable -> SideCondition variable
assumeTruePredicate predicate =
    assumeTrueCondition (Condition.fromPredicate predicate)

toPredicate
    :: InternalVariable variable
    => SideCondition variable
    -> Predicate variable
toPredicate condition@(SideCondition _) =
    Condition.toPredicate assumedTrue
  where
    SideCondition { assumedTrue } = condition

mapVariables
    :: (Ord variable1, Ord variable2)
    => (variable1 -> variable2)
    -> SideCondition variable1
    -> SideCondition variable2
mapVariables mapper condition@(SideCondition _) =
    SideCondition
        { assumedTrue = Condition.mapVariables mapper assumedTrue }
  where
    SideCondition { assumedTrue } = condition
