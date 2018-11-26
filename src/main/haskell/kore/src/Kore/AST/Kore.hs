{-|
Module      : Kore.AST.Kore
Description : Data Structures for representing the Kore language AST with
              unified constructs.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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

{-# LANGUAGE TemplateHaskell #-}

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
    , asUnifiedPattern
    , transformUnifiedPattern
    ) where

import Control.DeepSeq
       ( NFData (..) )
import Data.Deriving
       ( makeLiftCompare, makeLiftEq, makeLiftShowsPrec )
import Data.Functor.Classes
import Data.Functor.Foldable

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import qualified Kore.Domain.Builtin as Domain

{-|'UnifiedPattern' is joining the 'Meta' and 'Object' versions of 'Pattern', to
allow using toghether both 'Meta' and 'Object' patterns.
-}
data UnifiedPattern domain variable child where
    UnifiedMetaPattern
        :: !(Pattern Meta domain variable child)
        -> UnifiedPattern domain variable child

    UnifiedObjectPattern
        :: !(Pattern Object domain variable child)
        -> UnifiedPattern domain variable child

$(return [])  -- Begin a new definition group where UnifiedPattern is in scope.
              -- Without it, UnifiedPattern would be in scope for expressions,
              -- but not for quoting, so using ''UnifiedPattern below would
              -- fail.
              --
              -- Template Haskell limits the ways in which definitions can be
              -- mutually recursive; a quoted name must be defined in a
              -- previous definition group before it can be used.
              -- A top-level Template Haskell splice always starts a new
              -- definition group, even if the splice is empty, as is the
              -- case here.

instance
    ( NFData (Pattern Meta domain variable child)
    , NFData (Pattern Object domain variable child)
    ) =>
    NFData (UnifiedPattern domain variable child)
  where
    rnf =
        \case
            UnifiedMetaPattern metaP -> rnf metaP
            UnifiedObjectPattern objectP -> rnf objectP

instance
    ( Eq1 (Pattern Meta domain variable)
    , Eq1 (Pattern Object domain variable)
    ) =>
    Eq1 (UnifiedPattern domain variable)
  where
    liftEq = $(makeLiftEq ''UnifiedPattern)

instance
    ( Ord1 (Pattern Meta domain variable)
    , Ord1 (Pattern Object domain variable)
    ) =>
    Ord1 (UnifiedPattern domain variable)
  where
    liftCompare = $(makeLiftCompare ''UnifiedPattern)

instance
    ( Show1 (Pattern Meta domain variable)
    , Show1 (Pattern Object domain variable)
    ) =>
    Show1 (UnifiedPattern domain variable)
  where
    liftShowsPrec = $(makeLiftShowsPrec ''UnifiedPattern)

-- |View a 'Meta' or an 'Object' 'Pattern' as an 'UnifiedPattern'
asUnifiedPattern
    :: MetaOrObject level
    => Pattern level domain variable child
    -> UnifiedPattern domain variable child
asUnifiedPattern ph =
    case getMetaOrObjectPatternType ph of
        IsMeta -> UnifiedMetaPattern ph
        IsObject -> UnifiedObjectPattern ph

-- |Given a function appliable on all 'Meta' or 'Object' 'Pattern's,
-- apply it on an 'UnifiedPattern'.
transformUnifiedPattern
    ::  (forall level.
            MetaOrObject level =>
            Pattern level domain variable a -> b
        )
    -> (UnifiedPattern domain variable a -> b)
transformUnifiedPattern f =
    \case
        UnifiedMetaPattern metaP -> f metaP
        UnifiedObjectPattern objectP -> f objectP

deriving instance
    ( Eq (Pattern Meta domain variable child)
    , Eq (Pattern Object domain variable child)
    ) => Eq (UnifiedPattern domain variable child)

deriving instance
    ( Ord (Pattern Meta domain variable child)
    , Ord (Pattern Object domain variable child)
    ) => Ord (UnifiedPattern domain variable child)

deriving instance
    ( Show (Pattern Meta domain variable child)
    , Show (Pattern Object domain variable child)
    ) => Show (UnifiedPattern domain variable child)

deriving instance
    ( Functor (Pattern Meta domain variable)
    , Functor (Pattern Object domain variable)
    ) =>
    Functor (UnifiedPattern domain variable)

deriving instance
    ( Foldable (Pattern Meta domain variable)
    , Foldable (Pattern Object domain variable)
    ) =>
    Foldable (UnifiedPattern domain variable)

deriving instance
    ( Traversable (Pattern Meta domain variable)
    , Traversable (Pattern Object domain variable)
    ) =>
    Traversable (UnifiedPattern domain variable)

-- |'KorePattern' is a 'Fix' point of 'Pattern' comprising both
-- 'Meta' and 'Object' 'Pattern's
-- 'KorePattern' corresponds to the @pattern@ syntactic category from
-- the Semantics of K, Section 9.1.4 (Patterns).
type KorePattern domain variable = (Fix (UnifiedPattern domain variable))

pattern KoreMetaPattern
    :: Pattern Meta domain var (KorePattern domain var)
    -> KorePattern domain var
pattern KoreMetaPattern pat = Fix (UnifiedMetaPattern pat)

pattern KoreObjectPattern
    :: Pattern Object domain var (KorePattern domain var)
    -> KorePattern domain var
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

instance UnifiedPatternInterface UnifiedPattern where
    unifyPattern = asUnifiedPattern
    unifiedPatternApply = transformUnifiedPattern

-- |'CommonKorePattern' is the instantiation of 'KorePattern' with common
-- 'Variable's.
type CommonKorePattern = KorePattern Domain.Builtin Variable

-- |Given functions appliable to 'Meta' 'Pattern's and 'Object' 'Pattern's,
-- builds a combined function which can be applied on an 'KorePattern'.
applyKorePattern
    :: Functor domain
    => (Pattern Meta domain variable (KorePattern domain variable) -> b)
    -> (Pattern Object domain variable (KorePattern domain variable) -> b)
    -> (KorePattern domain variable -> b)
applyKorePattern metaT objectT korePattern =
    case project korePattern of
        UnifiedMetaPattern rp   -> metaT rp
        UnifiedObjectPattern rp -> objectT rp

type UnifiedSortVariable = Unified SortVariable
type UnifiedSort = Unified Sort
