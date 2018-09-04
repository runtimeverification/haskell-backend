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
    -- , pattern UnifiedMetaPattern
    -- , pattern UnifiedObjectPattern
    , asUnifiedPattern
    , transformUnifiedPattern
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Functor.Classes
import Data.Functor.Foldable
import GHC.Generics
       ( Generic )
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.Pretty
       ( Pretty (..) )




{-|'UnifiedPattern' is joining the 'Meta' and 'Object' versions of 'Pattern', to
allow using toghether both 'Meta' and 'Object' patterns.
-}

data UnifiedPattern domain variable child
 = UnifiedMetaPattern   (Pattern Meta domain variable child)
 | UnifiedObjectPattern (Pattern Object domain variable child)
     deriving ( Generic )

instance
    ( NFData child
    , NFData (variable Meta), NFData (variable Object)
    ) =>
    NFData (UnifiedPattern domain variable child)

instance (EqMetaOrObject variable) => Eq1 (UnifiedPattern domain variable) where
    liftEq liftedEq a b =
       case (a, b) of
          (UnifiedMetaPattern a', UnifiedMetaPattern b') ->
              liftEq liftedEq a' b'
          (UnifiedObjectPattern a', UnifiedObjectPattern b') ->
              liftEq liftedEq a' b'
          _ -> False

instance (ShowMetaOrObject variable) => Show1 (UnifiedPattern domain variable) where
    liftShowsPrec :: forall a.
                     (Int -> a -> ShowS) -> ([a] -> ShowS)
                  -> Int -> UnifiedPattern domain variable a
                  -> ShowS
    liftShowsPrec showsPrec_ showList_ _ p =
        applyUnifiedPattern
            (\t -> showString "UnifiedMetaPattern "   . go t)
            (\t -> showString "UnifiedObjectPattern " . go t)
            p
        where go 
                  :: (Show level, Show (variable level)) 
                  => Pattern level domain variable a 
                  -> ShowS
              go = liftShowsPrec showsPrec_ showList_ 0

instance (Pretty child, Pretty (variable Meta), Pretty (variable Object)) =>
    Pretty (UnifiedPattern domain variable child) where
    pretty (UnifiedObjectPattern a) = pretty a 
    pretty (UnifiedMetaPattern   a) = pretty a


-- |View a 'Meta' or an 'Object' 'Pattern' as an 'UnifiedPattern'
asUnifiedPattern
    :: (MetaOrObject level)
    => Pattern level domain variable child -> UnifiedPattern domain variable child
asUnifiedPattern p = case getMetaOrObjectPatternType p of 
    IsObject -> UnifiedObjectPattern p
    IsMeta   -> UnifiedMetaPattern   p

-- |Given a function appliable on all 'Meta' or 'Object' 'Pattern's,
-- apply it on an 'UnifiedPattern'.
transformUnifiedPattern
    :: (forall level . MetaOrObject level => Pattern level domain variable a -> b)
    -> UnifiedPattern domain variable a 
    -> b
transformUnifiedPattern f p' = case p' of 
    UnifiedObjectPattern p -> f @Object p
    UnifiedMetaPattern   p -> f @Meta   p

deriving instance
    ( Eq child
    , EqMetaOrObject variable
    ) => Eq (UnifiedPattern domain variable child)

deriving instance
    ( Show child
    , ShowMetaOrObject variable
    ) => Show (UnifiedPattern domain variable child)

instance Functor (UnifiedPattern domain variable) where
    fmap f = transformUnifiedPattern (asUnifiedPattern . fmap f)

instance Foldable (UnifiedPattern domain variable) where
    foldMap f = transformUnifiedPattern (foldMap f)

instance Traversable (UnifiedPattern domain variable) where
    sequenceA = transformUnifiedPattern (fmap asUnifiedPattern . sequenceA)

-- |'KorePattern' is a 'Fix' point of 'Pattern' comprising both
-- 'Meta' and 'Object' 'Pattern's
-- 'KorePattern' corresponds to the @pattern@ syntactic category from
-- the Semantics of K, Section 9.1.4 (Patterns).
type KorePattern domain variable = (Fix (UnifiedPattern domain variable))

pattern KoreMetaPattern
    :: Pattern Meta domain var (KorePattern domain var) -> KorePattern domain var
pattern KoreMetaPattern pat = Fix (UnifiedMetaPattern pat)

pattern KoreObjectPattern
    :: Pattern Object domain var (KorePattern domain var) -> KorePattern domain var
pattern KoreObjectPattern pat = Fix (UnifiedObjectPattern pat)

{-# COMPLETE KoreMetaPattern, KoreObjectPattern #-}

-- |View a 'Meta' or an 'Object' 'Pattern' as a 'KorePattern'
asKorePattern
    :: (MetaOrObject level)
    => Pattern level domain variable (KorePattern domain variable)
    -> KorePattern domain variable
asKorePattern = Fix . asUnifiedPattern

-- |View a 'Meta' 'Pattern' as a 'KorePattern'
asMetaKorePattern
    :: Pattern Meta domain variable (KorePattern domain variable)
    -> KorePattern domain variable
asMetaKorePattern = asKorePattern

-- |View a 'Object' 'Pattern' as a 'KorePattern'
asObjectKorePattern
    :: Pattern Object domain variable (KorePattern domain variable)
    -> KorePattern domain variable
asObjectKorePattern = asKorePattern

instance
    UnifiedPatternInterface UnifiedPattern
  where
    unifyPattern = asUnifiedPattern
    unifiedPatternApply = transformUnifiedPattern

-- |'CommonKorePattern' is the instantiation of 'KorePattern' with common
-- 'Variable's.
type CommonKorePattern = KorePattern KoreDomain Variable

applyUnifiedPattern
     :: (Pattern Meta domain variable child -> b)
     -> (Pattern Object domain variable child -> b)
     -> UnifiedPattern domain variable child
     -> b
applyUnifiedPattern metaT objectT p' = case p' of
    UnifiedObjectPattern p -> objectT p
    UnifiedMetaPattern   p -> metaT p


-- |Given functions appliable to 'Meta' 'Pattern's and 'Object' 'Pattern's,
-- builds a combined function which can be applied on an 'KorePattern'.
applyKorePattern
    :: (Pattern Meta domain variable (KorePattern domain variable) -> b)
    -> (Pattern Object domain variable (KorePattern domain variable) -> b)
    -> (KorePattern domain variable -> b)
applyKorePattern metaT objectT (Fix p') = 
    case p' of
      UnifiedObjectPattern p -> objectT p
      UnifiedMetaPattern   p -> metaT   p

type UnifiedSortVariable = Unified SortVariable
type UnifiedSort = Unified Sort

