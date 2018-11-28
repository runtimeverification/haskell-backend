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
    , KorePattern (..)
    , asKorePattern
    , asCommonKorePattern
    , UnifiedSortVariable
    , UnifiedSort
    , UnifiedPattern (..)
    , asUnifiedPattern
    , transformUnifiedPattern
    -- * Re-exports
    , Base, CofreeF (..)
    , module Kore.AST.Common
    , module Kore.AST.MetaOrObject
    ) where

import           Control.Comonad
import           Control.Comonad.Trans.Cofree
                 ( Cofree, CofreeF (..), ComonadCofree (..) )
import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Deriving
                 ( makeLiftCompare, makeLiftEq, makeLiftShowsPrec )
import           Data.Functor.Classes
import           Data.Functor.Compose
                 ( Compose (..) )
import           Data.Functor.Foldable
                 ( Base, Corecursive, Recursive )
import qualified Data.Functor.Foldable as Recursive
import           Data.Functor.Identity
                 ( Identity (..) )
import           Data.Hashable
                 ( Hashable (..) )
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Common hiding
                 ( castMetaDomainValues, castVoidDomainValues, mapDomainValues,
                 mapVariables, traverseVariables )
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

instance
    ( Hashable child
    , Hashable (var Meta)
    , Hashable (var Object)
    , Hashable (dom child)
    ) => Hashable (UnifiedPattern dom var child) where
    hashWithSalt salt =
        \case
            UnifiedMetaPattern metaP ->
                salt `hashWithSalt` (0::Int) `hashWithSalt` metaP
            UnifiedObjectPattern objectP ->
                salt `hashWithSalt` (1::Int) `hashWithSalt` objectP

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


{- | The abstract syntax of Kore.

@KorePattern@ covers the 'Object' and 'Meta' levels of Kore, corresponding to
the syntactic category @pattern@ in The Semantics of K, Section 9.1.4
(Patterns).

@dom@ is the type of domain values; see "Kore.Domain.External" and
"Kore.Domain.Builtin".

@var@ is the family of variable types, parameterized by level.

@ann@ is the type of annotations decorating each node of the abstract syntax
tree. @KorePattern@ is a 'Traversable' 'Comonad' over the type of annotations.

-}
newtype KorePattern
    (dom :: * -> *)
    (var :: * -> *)
    (ann :: *)
  =
    KorePattern { getKorePattern :: Cofree (UnifiedPattern dom var) ann }
    deriving (Foldable, Functor, Generic, Traversable)

instance
    ( Eq ann
    , EqMetaOrObject var
    , Eq1 dom, Functor dom
    ) =>
    Eq (KorePattern dom var ann)
  where
    (==) = eqWorker
      where
        eqWorker
            (Recursive.project -> ann1 :< pat1)
            (Recursive.project -> ann2 :< pat2)
          =
            ann1 == ann2 && liftEq eqWorker pat1 pat2

instance
    ( Ord ann
    , OrdMetaOrObject var
    , Ord1 dom, Functor dom
    ) =>
    Ord (KorePattern dom var ann)
  where
    compare = compareWorker
      where
        compareWorker
            (Recursive.project -> ann1 :< pat1)
            (Recursive.project -> ann2 :< pat2)
          =
            compare ann1 ann2 <> liftCompare compareWorker pat1 pat2

deriving instance
    ( Show ann
    , ShowMetaOrObject var
    , Show (dom child)
    , child ~ Cofree (UnifiedPattern dom var) ann
    ) =>
    Show (KorePattern dom var ann)

instance
    ( Functor dom
    , Hashable ann
    , Hashable (var Meta)
    , Hashable (var Object)
    , Hashable (dom child)
    , child ~ KorePattern dom var ann
    ) =>
    Hashable (KorePattern dom var ann)
  where
    hashWithSalt salt (Recursive.project -> ann :< pat) =
        salt `hashWithSalt` ann `hashWithSalt` pat

instance
    ( Functor dom
    , NFData ann
    , NFData (var Meta)
    , NFData (var Object)
    , NFData (dom child)
    , child ~ KorePattern dom var ann
    ) =>
    NFData (KorePattern dom var ann)
  where
    rnf (Recursive.project -> ann :< pat) =
        rnf ann `seq` rnf pat `seq` ()

type instance Base (KorePattern dom var ann) =
    CofreeF (UnifiedPattern dom var) ann

instance Functor dom => Recursive (KorePattern dom var ann) where
    project (KorePattern embedded) =
        case Recursive.project embedded of
            Compose (Identity projected) -> KorePattern <$> projected

instance Functor dom => Corecursive (KorePattern dom var ann) where
    embed projected =
        (KorePattern . Recursive.embed . Compose . Identity)
            (getKorePattern <$> projected)

-- | View an annotated 'Meta' or 'Object' 'Pattern' as a 'KorePattern'
asKorePattern
    :: (Functor dom, MetaOrObject lvl)
    => CofreeF (Pattern lvl dom var) ann (KorePattern dom var ann)
    -> KorePattern dom var ann
asKorePattern (ann :< pat) =
    Recursive.embed (ann :< asUnifiedPattern pat)

instance Functor dom => Comonad (KorePattern dom var) where
    extract (KorePattern a) = extract a
    duplicate (KorePattern a) = KorePattern (extend KorePattern a)
    extend extending (KorePattern a) =
        KorePattern (extend (extending . KorePattern) a)

instance
    Functor dom =>
    ComonadCofree (UnifiedPattern dom var) (KorePattern dom var)
  where
    unwrap (KorePattern a) = KorePattern <$> unwrap a

-- | View a 'Meta' or 'Object' 'Pattern' as a 'KorePattern'
asCommonKorePattern
    :: MetaOrObject lvl
    => Pattern lvl Domain.Builtin Variable CommonKorePattern
    -> CommonKorePattern
asCommonKorePattern pat = asKorePattern (mempty :< pat)

instance UnifiedPatternInterface UnifiedPattern where
    unifyPattern = asUnifiedPattern
    unifiedPatternApply = transformUnifiedPattern

-- |'CommonKorePattern' is the instantiation of 'KorePattern' with common
-- 'Variable's.
type CommonKorePattern = KorePattern Domain.Builtin Variable ()

type UnifiedSortVariable = Unified SortVariable
type UnifiedSort = Unified Sort
