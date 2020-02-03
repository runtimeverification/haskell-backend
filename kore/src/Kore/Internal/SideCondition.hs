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
    , toRepresentation
    ) where

import Prelude.Kore

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
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition.Representation
    ( fromText
    )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    , unparseToText
    )
import qualified Pretty
import qualified SQL

{-| Side condition used in the evaluation context.

It is not added to the result.

It is usually used to remove infeasible branches, but it may also be used for
other purposes, say, to remove redundant parts of the result predicate.
-}
data SideCondition variable =
    SideCondition
        { representation :: !SideCondition.Representation
        , assumedTrue :: !(Condition variable)
        }
    deriving (Eq, Show)

instance InternalVariable variable => SQL.Column (SideCondition variable) where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

instance TopBottom (SideCondition variable) where
    isTop sideCondition@(SideCondition _ _) =
        isTop assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition
    isBottom sideCondition@(SideCondition _ _) =
        isBottom assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

instance InternalVariable variable
    => HasFreeVariables (SideCondition variable) variable
  where
    freeVariables sideCondition@(SideCondition _ _) =
        freeVariables assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

instance InternalVariable variable => Unparse (SideCondition variable) where
    unparse sideCondition@(SideCondition _ _) =
        unparse assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

    unparse2 sideCondition@(SideCondition _ _) =
        unparse2 assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

top :: InternalVariable variable => SideCondition variable
top = fromCondition Condition.top

-- | A 'top' 'Condition' for refactoring which should eventually be removed.
topTODO :: InternalVariable variable => SideCondition variable
topTODO = top

andCondition
    :: InternalVariable variable
    => SideCondition variable
    -> Condition variable
    -> SideCondition variable
andCondition SideCondition {assumedTrue} newCondition =
    SideCondition
        { representation = toRepresentationCondition merged
        , assumedTrue = merged
        }
  where
    merged = assumedTrue `Condition.andCondition` newCondition

assumeTrueCondition
    :: InternalVariable variable => Condition variable -> SideCondition variable
assumeTrueCondition = fromCondition

assumeTruePredicate
    :: InternalVariable variable => Predicate variable -> SideCondition variable
assumeTruePredicate predicate =
    assumeTrueCondition (Condition.fromPredicate predicate)

toPredicate
    :: InternalVariable variable
    => SideCondition variable
    -> Predicate variable
toPredicate condition@(SideCondition _ _) =
    Condition.toPredicate assumedTrue
  where
    SideCondition { assumedTrue } = condition

toRepresentation :: SideCondition variable -> SideCondition.Representation
toRepresentation SideCondition { representation } = representation

mapVariables
    :: (Ord variable1, InternalVariable variable2)
    => (variable1 -> variable2)
    -> SideCondition variable1
    -> SideCondition variable2
mapVariables mapper condition@(SideCondition _ _) =
    fromCondition (Condition.mapVariables mapper assumedTrue)
  where
    SideCondition { assumedTrue } = condition

fromCondition
    :: InternalVariable variable => Condition variable -> SideCondition variable
fromCondition assumedTrue =
    SideCondition
        { representation = toRepresentationCondition assumedTrue
        , assumedTrue
        }

toRepresentationCondition
    :: InternalVariable variable
    => Condition variable
    -> SideCondition.Representation
toRepresentationCondition condition =
    SideCondition.Representation.fromText $ unparseToText condition
