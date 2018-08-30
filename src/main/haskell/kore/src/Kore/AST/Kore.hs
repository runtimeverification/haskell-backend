{-|
Module      : Kore.AST.Kore
Description : Data Structures for representing the Kore language AST with
              unified constructs.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort Object' or 'Sort Meta')

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Kore.AST.Kore
    ( CommonKorePattern
    , KorePattern
    , pattern KoreMetaPattern
    , pattern KoreObjectPattern
    , asKorePattern
    , asMetaKorePattern
    , asObjectKorePattern
    , applyKorePattern
    , UnifiedSortVariable
    , UnifiedSort
    , UnifiedPattern (..)
    , pattern UnifiedMetaPattern
    , pattern UnifiedObjectPattern
    , asUnifiedPattern
    , transformUnifiedPattern
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Functor.Classes
import Data.Functor.Foldable
import GHC.Generics
       ( Generic )

import Data.Functor.Impredicative
       ( Rotate31 (..) )
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.Pretty
       ( Pretty (..) )



{-|'UnifiedPattern' is joining the 'Meta' and 'Object' versions of 'Pattern', to
allow using toghether both 'Meta' and 'Object' patterns.
-}
newtype UnifiedPattern variable child = UnifiedPattern
    { getUnifiedPattern :: Unified (Rotate31 Pattern variable child) }
  deriving ( Generic )

pattern UnifiedMetaPattern :: Pattern Meta var child -> UnifiedPattern var child
pattern UnifiedMetaPattern pat = UnifiedPattern (UnifiedMeta (Rotate31 pat))

pattern UnifiedObjectPattern :: Pattern Object var child -> UnifiedPattern var child
pattern UnifiedObjectPattern pat = UnifiedPattern (UnifiedObject (Rotate31 pat))

{-# COMPLETE UnifiedMetaPattern, UnifiedObjectPattern #-}

instance
    ( NFData child
    , NFData (variable Meta), NFData (variable Object)
    ) =>
    NFData (UnifiedPattern variable child)

instance (EqMetaOrObject variable) => Eq1 (UnifiedPattern variable) where
    liftEq liftedEq (UnifiedPattern a) (UnifiedPattern b) =
       case (a, b) of
          (UnifiedMeta a', UnifiedMeta b') ->
              liftEq liftedEq (unRotate31 a') (unRotate31 b')
          (UnifiedObject a', UnifiedObject b') ->
              liftEq liftedEq (unRotate31 a') (unRotate31 b')
          _ -> False

instance (ShowMetaOrObject variable) => Show1 (UnifiedPattern variable) where
    liftShowsPrec :: forall a.
                     (Int -> a -> ShowS) -> ([a] -> ShowS)
                  -> Int -> UnifiedPattern variable a
                  -> ShowS
    liftShowsPrec showsPrec_ showList_ _ up =
        showString "UnifiedPattern { getUnifiedPattern = "
        . applyUnified
            (\t -> showString "UnifiedMeta " . liftShowsPrecRotate31 t)
            (\t -> showString "UnifiedObject " . liftShowsPrecRotate31 t)
            (getUnifiedPattern up)
        . showString " }"
      where
        liftShowsPrecRotate31 :: (Show level, Show (variable level))
                              => Rotate31 Pattern variable a level
                              -> ShowS
        liftShowsPrecRotate31 r =
            showString "Rotate31 { unRotate31 = "
            . liftShowsPrec showsPrec_ showList_ 0 (unRotate31 r)
            . showString " }"

instance (Pretty child, Pretty (variable Meta), Pretty (variable Object)) =>
    Pretty (UnifiedPattern variable child) where
    pretty = applyUnified (pretty . unRotate31) (pretty . unRotate31) . getUnifiedPattern

-- |View a 'Meta' or an 'Object' 'Pattern' as an 'UnifiedPattern'
asUnifiedPattern
    :: (MetaOrObject level)
    => Pattern level variable child -> UnifiedPattern variable child
asUnifiedPattern = UnifiedPattern . asUnified . Rotate31

-- |Given a function appliable on all 'Meta' or 'Object' 'Pattern's,
-- apply it on an 'UnifiedPattern'.
transformUnifiedPattern
    :: (forall level . MetaOrObject level => Pattern level variable a -> b)
    -> (UnifiedPattern variable a -> b)
transformUnifiedPattern f =
    transformUnified (f . unRotate31) . getUnifiedPattern

deriving instance
    ( Eq child
    , EqMetaOrObject variable
    ) => Eq (UnifiedPattern variable child)

deriving instance
    ( Show child
    , ShowMetaOrObject variable
    ) => Show (UnifiedPattern variable child)

instance Functor (UnifiedPattern variable) where
    fmap f =
        UnifiedPattern
        . mapUnified (Rotate31 . fmap f . unRotate31)
        . getUnifiedPattern
instance Foldable (UnifiedPattern variable) where
    foldMap f =
        transformUnified (foldMap f . unRotate31)
        . getUnifiedPattern
instance Traversable (UnifiedPattern variable) where
    sequenceA =
        fmap UnifiedPattern
        . sequenceUnified
            (fmap Rotate31 . sequenceA . unRotate31)
        . getUnifiedPattern

-- |'KorePattern' is a 'Fix' point of 'Pattern' comprising both
-- 'Meta' and 'Object' 'Pattern's
-- 'KorePattern' corresponds to the @pattern@ syntactic category from
-- the Semantics of K, Section 9.1.4 (Patterns).
type KorePattern variable = (Fix (UnifiedPattern variable))

pattern KoreMetaPattern
    :: Pattern Meta var (KorePattern var) -> KorePattern var
pattern KoreMetaPattern pat = Fix (UnifiedMetaPattern pat)

pattern KoreObjectPattern
    :: Pattern Object var (KorePattern var) -> KorePattern var
pattern KoreObjectPattern pat = Fix (UnifiedObjectPattern pat)

{-# COMPLETE KoreMetaPattern, KoreObjectPattern #-}

-- |View a 'Meta' or an 'Object' 'Pattern' as a 'KorePattern'
asKorePattern
    :: (MetaOrObject level)
    => Pattern level variable (KorePattern variable)
    -> KorePattern variable
asKorePattern = Fix . asUnifiedPattern

-- |View a 'Meta' 'Pattern' as a 'KorePattern'
asMetaKorePattern
    :: Pattern Meta variable (KorePattern variable)
    -> KorePattern variable
asMetaKorePattern = asKorePattern

-- |View a 'Object' 'Pattern' as a 'KorePattern'
asObjectKorePattern
    :: Pattern Object variable (KorePattern variable)
    -> KorePattern variable
asObjectKorePattern = asKorePattern

instance
    UnifiedPatternInterface UnifiedPattern
  where
    unifyPattern = asUnifiedPattern
    unifiedPatternApply = transformUnifiedPattern

-- |'CommonKorePattern' is the instantiation of 'KorePattern' with common
-- 'Variable's.
type CommonKorePattern = KorePattern Variable

-- |Given functions appliable to 'Meta' 'Pattern's and 'Object' 'Pattern's,
-- builds a combined function which can be applied on an 'KorePattern'.
applyKorePattern
    :: (Pattern Meta variable (KorePattern variable) -> b)
    -> (Pattern Object variable (KorePattern variable) -> b)
    -> (KorePattern variable -> b)
applyKorePattern metaT objectT korePattern =
    case getUnifiedPattern (project korePattern) of
        UnifiedMeta rp   -> metaT (unRotate31 rp)
        UnifiedObject rp -> objectT (unRotate31 rp)

type UnifiedSortVariable = Unified SortVariable
type UnifiedSort = Unified Sort
