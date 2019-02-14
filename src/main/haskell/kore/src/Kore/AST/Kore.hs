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
import qualified Control.Comonad.Trans.Env as Env
import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Bifunctor as Bifunctor
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
import           Kore.Sort
import           Kore.Unparser
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
    {-# INLINE liftEq #-}

instance
    ( Ord1 (Pattern Meta domain variable)
    , Ord1 (Pattern Object domain variable)
    ) =>
    Ord1 (UnifiedPattern domain variable)
  where
    liftCompare = $(makeLiftCompare ''UnifiedPattern)
    {-# INLINE liftCompare #-}

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
    {-# INLINE hashWithSalt #-}

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

instance
    ( Unparse (variable Meta)
    , Unparse (variable Object)
    , Unparse (domain child)
    , Unparse child
    ) =>
    Unparse (UnifiedPattern domain variable child)
  where
    unparse =
        \case
            UnifiedMetaPattern pat -> unparse pat
            UnifiedObjectPattern pat -> unparse pat

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
    {-# INLINE (==) #-}

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
    {-# INLINE compare #-}

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
    {-# INLINE hashWithSalt #-}

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

instance
    ( Functor domain
    , Unparse (variable Meta)
    , Unparse (variable Object)
    , Unparse (domain self)
    , self ~ KorePattern domain variable annotation
    ) =>
    Unparse (KorePattern domain variable annotation)
  where
    unparse (Recursive.project -> _ :< pat) = unparse pat

type instance Base (KorePattern domain variable annotation) =
    CofreeF (UnifiedPattern domain variable) annotation

-- This instance implements all class functions for the PurePattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Recursive (KorePattern domain variable annotation)
  where
    project = \(KorePattern embedded) ->
        case Recursive.project embedded of
            Compose (Identity projected) -> KorePattern <$> projected
    {-# INLINE project #-}

    -- This specialization is particularly important: The default implementation
    -- of 'cata' in terms of 'project' would involve an extra call to 'fmap' at
    -- every level of the tree due to the implementation of 'project' above.
    cata alg = \(KorePattern fixed) ->
        Recursive.cata
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE cata #-}

    para alg = \(KorePattern fixed) ->
        Recursive.para
            (\(Compose (Identity base)) ->
                alg (Bifunctor.first KorePattern <$> base)
            )
            fixed
    {-# INLINE para #-}

    gpara dist alg = \(KorePattern fixed) ->
        Recursive.gpara
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> alg (Env.local KorePattern <$> base))
            fixed
    {-# INLINE gpara #-}

    prepro pre alg = \(KorePattern fixed) ->
        Recursive.prepro
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE prepro #-}

    gprepro dist pre alg = \(KorePattern fixed) ->
        Recursive.gprepro
            (\(Compose (Identity base)) -> Compose . Identity <$> dist base)
            (\(Compose (Identity base)) -> (Compose . Identity) (pre base))
            (\(Compose (Identity base)) -> alg base)
            fixed
    {-# INLINE gprepro #-}

-- This instance implements all class functions for the PurePattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Corecursive (KorePattern domain variable annotation)
  where
    embed = \projected ->
        (KorePattern . Recursive.embed . Compose . Identity)
            (getKorePattern <$> projected)
    {-# INLINE embed #-}

    ana coalg = KorePattern . ana0
      where
        ana0 =
            Recursive.ana (Compose . Identity . coalg)
    {-# INLINE ana #-}

    apo coalg = KorePattern . apo0
      where
        apo0 =
            Recursive.apo
                (\a ->
                     (Compose . Identity)
                        (Bifunctor.first getKorePattern <$> coalg a)
                )
    {-# INLINE apo #-}

    postpro post coalg = KorePattern . postpro0
      where
        postpro0 =
            Recursive.postpro
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE postpro #-}

    gpostpro dist post coalg = KorePattern . gpostpro0
      where
        gpostpro0 =
            Recursive.gpostpro
                (Compose . Identity . dist . (<$>) (runIdentity . getCompose))
                (\(Compose (Identity base)) -> (Compose . Identity) (post base))
                (Compose . Identity . coalg)
    {-# INLINE gpostpro #-}

-- This instance implements all class functions for the PurePattern newtype
-- because the their implementations for the inner type may be specialized.
instance
    Functor domain =>
    Comonad (KorePattern domain variable)
  where
    extract = \(KorePattern fixed) -> extract fixed
    {-# INLINE extract #-}
    duplicate = \(KorePattern fixed) -> KorePattern (extend KorePattern fixed)
    {-# INLINE duplicate #-}
    extend extending = \(KorePattern fixed) ->
        KorePattern (extend (extending . KorePattern) fixed)
    {-# INLINE extend #-}

instance
    Functor domain =>
    ComonadCofree
        (UnifiedPattern domain variable)
        (KorePattern domain variable)
  where
    unwrap = \(KorePattern fixed) -> KorePattern <$> unwrap fixed
    {-# INLINE unwrap #-}

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
type VerifiedKorePattern =
    KorePattern Domain.Builtin Variable (Unified (Valid (Unified Variable)))

type UnifiedSortVariable = Unified SortVariable
type UnifiedSort = Unified Sort
