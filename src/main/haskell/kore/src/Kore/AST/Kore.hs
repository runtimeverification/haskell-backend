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
    ( KorePattern (..)
    , CommonKorePattern
    , VerifiedKorePattern
    , asKorePattern
    , eraseAnnotations
    , asCommonKorePattern
    , UnifiedSortVariable
    , UnifiedSort
    , UnifiedPattern (..)
    , asUnifiedPattern
    , transformUnifiedPattern
    -- * Re-exports
    , Base, CofreeF (..)
    , module Kore.AST.Common
    , module Kore.AST.Identifier
    , module Kore.AST.MetaOrObject
    , module Kore.Annotation.Valid
    , module Kore.Sort
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

import qualified Kore.Annotation.Null as Annotation
import           Kore.Annotation.Valid
import           Kore.AST.Common hiding
                 ( castMetaDomainValues, castVoidDomainValues, mapDomainValues,
                 mapVariables, traverseVariables )
import           Kore.AST.Identifier
import           Kore.AST.MetaOrObject
import qualified Kore.Domain.Builtin as Domain
import           Kore.Reflect
                 ( Reflectable, Reflectable1, ReflectableHelper )
import           Kore.Sort
import           Template.Tools
                 ( newDefinitionGroup )

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
  deriving (Generic)

instance
    ( Reflectable (variable Meta), Reflectable (variable Object)
    , Reflectable child
    , Reflectable (domain child)
    ) => Reflectable (UnifiedPattern domain variable child)

instance
    ( Reflectable (variable Meta), Reflectable (variable Object)
    , Reflectable (domain ReflectableHelper)
    , Functor domain
    ) => Reflectable1 (UnifiedPattern domain variable)

$newDefinitionGroup
-- Begin a new definition group where UnifiedPattern is in scope.

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
    , Hashable (variable Meta)
    , Hashable (variable Object)
    , Hashable (domain child)
    ) => Hashable (UnifiedPattern domain variable child) where
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
    (domain :: * -> *)
    (variable :: * -> *)
    (annotation :: *)
  =
    KorePattern
        { getKorePattern :: Cofree (UnifiedPattern domain variable) annotation }
    deriving (Foldable, Functor, Generic, Traversable)

instance
    ( Reflectable (variable Meta), Reflectable (variable Object)
    , Functor domain
    , Reflectable (domain ReflectableHelper)
    , Reflectable annotation
    ) => Reflectable (KorePattern domain variable annotation)

instance
    ( EqMetaOrObject variable
    , Eq1 domain, Functor domain
    ) =>
    Eq (KorePattern domain variable annotation)
  where
    (==) = eqWorker
      where
        eqWorker
            (Recursive.project -> _ :< pat1)
            (Recursive.project -> _ :< pat2)
          =
            liftEq eqWorker pat1 pat2

instance
    ( OrdMetaOrObject variable
    , Ord1 domain, Functor domain
    ) =>
    Ord (KorePattern domain variable annotation)
  where
    compare = compareWorker
      where
        compareWorker
            (Recursive.project -> _ :< pat1)
            (Recursive.project -> _ :< pat2)
          =
            liftCompare compareWorker pat1 pat2

deriving instance
    ( Show annotation
    , ShowMetaOrObject variable
    , Show1 domain
    ) =>
    Show (KorePattern domain variable annotation)

instance
    ( Functor domain
    , Hashable (variable Meta)
    , Hashable (variable Object)
    , Hashable (domain child)
    , child ~ KorePattern domain variable annotation
    ) =>
    Hashable (KorePattern domain variable annotation)
  where
    hashWithSalt salt (Recursive.project -> _ :< pat) = hashWithSalt salt pat

instance
    ( Functor domain
    , NFData annotation
    , NFData (variable Meta)
    , NFData (variable Object)
    , NFData (domain child)
    , child ~ KorePattern domain variable annotation
    ) =>
    NFData (KorePattern domain variable annotation)
  where
    rnf (Recursive.project -> annotation :< pat) =
        rnf annotation `seq` rnf pat `seq` ()

type instance Base (KorePattern domain variable annotation) =
    CofreeF (UnifiedPattern domain variable) annotation

instance
    Functor domain =>
    Recursive (KorePattern domain variable annotation)
  where
    project (KorePattern embedded) =
        case Recursive.project embedded of
            Compose (Identity projected) -> KorePattern <$> projected

instance
    Functor domain =>
    Corecursive (KorePattern domain variable annotation)
  where
    embed projected =
        (KorePattern . Recursive.embed . Compose . Identity)
            (getKorePattern <$> projected)

-- | View an annotated 'Meta' or 'Object' 'Pattern' as a 'KorePattern'
asKorePattern
    :: (Functor domain, MetaOrObject level)
    => CofreeF
        (Pattern level domain variable)
        (annotation level)
        (KorePattern domain variable (Unified annotation))
    -> KorePattern domain variable (Unified annotation)
asKorePattern (ann :< pat) =
    Recursive.embed (asUnified ann :< asUnifiedPattern pat)

-- | Erase the annotations from any 'KorePattern'.
eraseAnnotations
    :: Functor domain
    => KorePattern domain variable erased
    -> KorePattern domain variable (Unified Annotation.Null)
eraseAnnotations =
    Recursive.unfold eraseAnnotationsWorker
  where
    eraseAnnotationsWorker (Recursive.project -> _ :< unified) =
        case unified of
            UnifiedMetaPattern _ -> UnifiedMeta Annotation.Null :< unified
            UnifiedObjectPattern _ -> UnifiedObject Annotation.Null :< unified

instance Functor dom => Comonad (KorePattern dom var) where
    extract (KorePattern a) = extract a
    duplicate (KorePattern a) = KorePattern (extend KorePattern a)
    extend extending (KorePattern a) =
        KorePattern (extend (extending . KorePattern) a)

instance
    Functor domain =>
    ComonadCofree (UnifiedPattern domain variable) (KorePattern domain variable)
  where
    unwrap (KorePattern a) = KorePattern <$> unwrap a

-- | View a 'Meta' or 'Object' 'Pattern' as a 'KorePattern'
asCommonKorePattern
    :: MetaOrObject level
    => Pattern level Domain.Builtin Variable CommonKorePattern
    -> CommonKorePattern
asCommonKorePattern pat = asKorePattern (mempty :< pat)

instance UnifiedPatternInterface UnifiedPattern where
    unifyPattern = asUnifiedPattern
    unifiedPatternApply = transformUnifiedPattern

-- |'CommonKorePattern' is the instantiation of 'KorePattern' with common
-- 'Variable's.
type CommonKorePattern =
    KorePattern Domain.Builtin Variable (Unified Annotation.Null)

-- | A 'CommonKorePattern' that has passed verification.
type VerifiedKorePattern = KorePattern Domain.Builtin Variable (Unified Valid)

type UnifiedSortVariable = Unified SortVariable
type UnifiedSort = Unified Sort
