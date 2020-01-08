{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Internal.SideCondition
    ( SideCondition  -- Constructor not exported on purpose
    , andCondition
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

{-| Side condition used in the evaluation context.

It is not added to the result.

It is usually used to remove infeasible branches, but it may also be used for
other purposes, say, to remove redundant parts of the result predicate.
-}
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

andCondition
    :: InternalVariable variable
    => SideCondition variable
    -> Condition variable
    -> SideCondition variable
andCondition sideCondition@SideCondition {assumedTrue} newCondition =
    sideCondition
        { assumedTrue = assumedTrue `Condition.andCondition` newCondition }

assumeTrueCondition :: Condition variable -> SideCondition variable
assumeTrueCondition condition =
    SideCondition { assumedTrue = condition }

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
