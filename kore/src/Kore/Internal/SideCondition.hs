{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

-- For instance Applicative:
{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.SideCondition
    ( SideCondition  -- Constructor not exported on purpose
    , fromCondition
    , fromPredicate
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

import Control.DeepSeq
    ( NFData
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition.SideCondition as SideCondition
import Kore.Internal.Variable
    ( InternalVariable
    , SubstitutionOrd
    )
import Kore.Syntax.Variable
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )
import qualified Pretty
import qualified SQL

{-| Side condition used in the evaluation context.

It is not added to the result.

It is usually used to remove infeasible branches, but it may also be used for
other purposes, say, to remove redundant parts of the result predicate.
-}
newtype SideCondition variable =
    SideCondition
        { assumedTrue :: MultiAnd (Predicate variable)
        }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving newtype (Semigroup, Monoid)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug)

instance
    (Debug variable, Diff variable, Ord variable, SubstitutionOrd variable)
    => Diff (SideCondition variable)

instance InternalVariable variable => SQL.Column (SideCondition variable) where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . unparse

instance TopBottom (SideCondition variable) where
    isTop sideCondition@(SideCondition _) =
        isTop assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition
    isBottom sideCondition@(SideCondition _) =
        isBottom assumedTrue
      where
        SideCondition {assumedTrue} = sideCondition

instance Ord variable => HasFreeVariables (SideCondition variable) variable
  where
    freeVariables (SideCondition multiAnd) =
        freeVariables multiAnd

instance InternalVariable variable => Unparse (SideCondition variable) where
    unparse = unparse . toPredicate
    unparse2 = unparse2 . toPredicate

instance From (SideCondition variable) (MultiAnd (Predicate variable))
  where
    from condition@(SideCondition _) = assumedTrue condition
    {-# INLINE from #-}

instance From (MultiAnd (Predicate variable)) (SideCondition variable)
  where
    from = SideCondition
    {-# INLINE from #-}

instance
    InternalVariable variable
    => From (SideCondition variable) (Predicate variable)
  where
    from = toPredicate
    {-# INLINE from #-}

instance
    InternalVariable variable
    => From (Predicate variable) (SideCondition variable)
  where
    from = fromPredicate
    {-# INLINE from #-}

instance InternalVariable variable =>
    From (Condition variable) (SideCondition variable)
  where
    from = fromCondition
    {-# INLINE from #-}

instance InternalVariable variable =>
    From (SideCondition variable) (Condition variable)
  where
    from = Condition.fromPredicate . toPredicate
    {-# INLINE from #-}

top :: SideCondition variable
top = SideCondition MultiAnd.top

-- | A 'top' 'Condition' for refactoring which should eventually be removed.
topTODO :: SideCondition variable
topTODO = top

andCondition
    :: InternalVariable variable
    => SideCondition variable
    -> Condition variable
    -> SideCondition variable
andCondition
    sideCondition
    (from @(Condition _) @(SideCondition _) -> newSideCondition)
  =
    newSideCondition <> sideCondition

assumeTrueCondition
    :: InternalVariable variable
    => Condition variable
    -> SideCondition variable
assumeTrueCondition = fromCondition

assumeTruePredicate
    :: InternalVariable variable
    => Predicate variable
    -> SideCondition variable
assumeTruePredicate = fromPredicate

toPredicate
    :: InternalVariable variable
    => SideCondition variable
    -> Predicate variable
toPredicate condition@(SideCondition _) =
    MultiAnd.toPredicate assumedTrue
  where
    SideCondition { assumedTrue } = condition

fromPredicate
    :: InternalVariable variable
    => Predicate variable
    -> SideCondition variable
fromPredicate = SideCondition . MultiAnd.fromPredicate

mapVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> SideCondition variable1
    -> SideCondition variable2
mapVariables adj condition@(SideCondition _) =
    MultiAnd.map (Predicate.mapVariables adj) assumedTrue
    & SideCondition
  where
    SideCondition { assumedTrue } = condition

fromCondition
    :: InternalVariable variable
    => Condition variable
    -> SideCondition variable
fromCondition = fromPredicate . Condition.toPredicate

toRepresentation
    :: InternalVariable variable
    => SideCondition variable
    -> SideCondition.Representation
toRepresentation =
    mkRepresentation
    . mapVariables @_ @VariableName (pure toVariableName)
