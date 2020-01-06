{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.Simplified
    ( Simplified (..)
    , isSimplified
    , isFullySimplified
    , simplifiedTo
    , fullySimplified
    , simplifiedConditionally
    ) where

import Control.DeepSeq
import Data.Foldable as Foldable
import Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import GHC.Stack
    ( HasCallStack
    )

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Domain.Builtin
import Kore.Internal.Inj
    ( Inj
    )
import qualified Kore.Internal.Inj as Inj
import Kore.Internal.InternalBytes
    ( InternalBytes
    )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Syntax
    ( And
    , Application
    , Bottom
    , Ceil
    , Const
    , DomainValue
    , Equals
    , Exists
    , Floor
    , Forall
    , Iff
    , Implies
    , In
    , Inhabitant
    , Mu
    , Next
    , Not
    , Nu
    , Or
    , Rewrites
    , StringLiteral
    , Top
    )
import Kore.Variables.UnifiedVariable

{- How well simplified is a pattern.
-}
data Type
    = Fully
    | Partly
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Type

instance SOP.HasDatatypeInfo Type

instance Debug Type

instance Diff Type where
    diffPrec = diffPrecIgnore

instance NFData Type

instance Hashable Type

instance Semigroup Type
  where
    Partly <> _ = Partly
    _ <> Partly = Partly

    Fully <> Fully = Fully

instance Monoid Type where
    mempty = Fully

{- Under which condition is a pattern simplified.
-}
data Condition
    = Any
    | Condition !SideCondition.Representation
    | Unknown
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Condition

instance SOP.HasDatatypeInfo Condition

instance Debug Condition

instance Diff Condition where
    diffPrec = diffPrecIgnore

instance NFData Condition

instance Hashable Condition

instance Semigroup Condition
  where
    Unknown <> _ = Unknown
    _ <> Unknown = Unknown

    Any <> c = c
    c <> Any = c

    c@(Condition c1) <> Condition c2 =
        if c1 == c2
            then c
            else Unknown

instance Monoid Condition where
    mempty = Any

{- | A pattern is 'Simplified' if it has run through the simplifier.

The simplifier runs until we do not know how to simplify a pattern any more. A
pattern 'isSimplified' if re-applying the simplifier would return the same
pattern.

Most patterns are assumed un-simplified until marked otherwise, so the
simplified status is reset by any substitution under the pattern.
-}
data Simplified
    = Simplified !(Type, Condition)
    | NotSimplified
    deriving (Eq, GHC.Generic, Ord, Show)

{- |
data Simplified =
    Simplified
    -- ^ Fully simplified
  | PartlySimplified
    -- ^ From any path from the root to any leaf, one encounters a Simplified
    -- node, and travels only through `PartlySimplified` nodes until then.
  | SimplifiedFor !SideCondition.Representation
    -- ^ Simplified only under the given condition, i.e. if the condition
    -- changes, the node must be resimplified.
  | PartlySimplifiedFor !SideCondition.Representation
    -- ^ Similar to 'PartlySimplified'. On any path from the root to a leaf,
    -- one encounters one of 'Simplified', 'PartlySimplified' or 'SimplifiedFor'
    -- and travels only through `PartlySimplifiedFor` nodes until then.
  | NotSimplified
    deriving (Eq, GHC.Generic, Ord, Show)
 -}

instance Semigroup Simplified
  where
    NotSimplified <> _ = NotSimplified
    _ <> NotSimplified = NotSimplified

    Simplified (t1, c1) <> Simplified (t2, c2) = Simplified (t1 <> t2, c1 <> c2)

instance Monoid Simplified where
    mempty = Simplified (mempty, mempty)

instance SOP.Generic Simplified

instance SOP.HasDatatypeInfo Simplified

instance Debug Simplified

instance Diff Simplified where
    diffPrec = diffPrecIgnore

instance NFData Simplified

instance Hashable Simplified

simplifiedTo :: HasCallStack => Simplified -> Simplified -> Simplified
NotSimplified `simplifiedTo` NotSimplified = NotSimplified
_ `simplifiedTo` NotSimplified =
    error "Should not make sense to upgrade something else to NotSimplified."
NotSimplified `simplifiedTo` _ =
    error "Cannot upgrade NotSimplified to something else."

Simplified _ `simplifiedTo` s@(Simplified (Fully, Unknown)) = s
Simplified (_, Unknown) `simplifiedTo` Simplified (Fully, _) =
    Simplified (Fully, Unknown)

Simplified (_, Condition c1) `simplifiedTo` s@(Simplified (Fully, Condition c2))
  = if c1 == c2
    then s
    else Simplified (Fully, Unknown)
Simplified (_, Any) `simplifiedTo` s@(Simplified (Fully, Condition _)) = s

s@(Simplified (_, Condition _)) `simplifiedTo` Simplified (Fully, Any) = s
Simplified (_, Any) `simplifiedTo` s@(Simplified (Fully, Any)) = s

s1@(Simplified _) `simplifiedTo` s2@(Simplified (Partly, _)) = s1 <> s2

isSimplified :: SideCondition.Representation -> Simplified -> Bool
isSimplified _ (Simplified (Fully, Any)) = True
isSimplified currentCondition (Simplified (Fully, Condition condition)) =
    currentCondition == condition
isSimplified _ (Simplified (Fully, Unknown)) = False
isSimplified _ (Simplified (Partly, _)) = False
isSimplified _ NotSimplified = False

isFullySimplified :: Simplified -> Bool
isFullySimplified (Simplified (Fully, Any)) = True
isFullySimplified (Simplified (Fully, Condition _)) = False
isFullySimplified (Simplified (Fully, Unknown)) = False
isFullySimplified (Simplified (Partly, _)) = False
isFullySimplified NotSimplified = False

fullySimplified :: Simplified
fullySimplified = Simplified (Fully, Any)

simplifiedConditionally :: SideCondition.Representation -> Simplified
simplifiedConditionally c = Simplified (Fully, Condition c)

alwaysSimplified :: a -> Simplified
alwaysSimplified = const fullySimplified
{-# INLINE alwaysSimplified #-}

notSimplified :: Foldable a => a Simplified -> Simplified
notSimplified a
  | Foldable.null a = NotSimplified
  | otherwise = Foldable.fold a <> Simplified (Partly, Any)
{-# INLINE notSimplified #-}

instance Synthetic Simplified (Bottom sort) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Top sort) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const StringLiteral) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const InternalBytes) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Const (UnifiedVariable variable)) where
    synthetic = alwaysSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Exists sort variable) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Forall sort variable) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (And sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Or sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Not sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Application head) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Ceil sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Floor sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (DomainValue sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Equals sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (In sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Implies sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Iff sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Mu variable) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Nu variable) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Next sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Rewrites sort) where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified (Builtin key) where
    synthetic (BuiltinInt    _) = Simplified (Fully, Any)
    synthetic (BuiltinBool   _) = Simplified (Fully, Any)
    synthetic (BuiltinString _) = Simplified (Fully, Any)
    synthetic b@(BuiltinMap    _) = notSimplified b
    synthetic b@(BuiltinList   _) = notSimplified b
    synthetic b@(BuiltinSet    _) = notSimplified b
    {-# INLINE synthetic #-}

instance Synthetic Simplified Inhabitant where
    synthetic = notSimplified
    {-# INLINE synthetic #-}

instance Synthetic Simplified Inj where
    synthetic = synthetic . Inj.toApplication
    {-# INLINE synthetic #-}
