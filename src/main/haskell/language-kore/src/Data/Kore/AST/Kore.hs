{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE UndecidableInstances  #-}

{-|
Module      : Data.Kore.AST.Kore
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
module Data.Kore.AST.Kore
    ( KoreDefinition
    , KoreModule
    , KoreSentence
    , KoreSentenceAlias
    , KoreSentenceSymbol
    , KoreSentenceSort
    , KoreSentenceImport
    , KoreSentenceAxiom
    , UnifiedSentence (..)
    , applyUnifiedSentence
    , KoreAttributes
    , CommonKorePattern
    , KorePattern
    , asKorePattern
    , applyKorePattern
    , UnifiedSortVariable
    , UnifiedSort
    , UnifiedPattern (..)
    , asUnifiedPattern
    , transformUnifiedPattern
    , transformUnifiedPatternM
    ) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.HaskellExtensions (Rotate31 (..), Rotate41 (..))

import           Data.Fix

{-|'UnifiedPattern' corresponds to the @pattern@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
newtype UnifiedPattern variable child = UnifiedPattern
    { getUnifiedPattern :: Unified (Rotate31 Pattern variable child) }

asUnifiedPattern
    :: (MetaOrObject level)
    => Pattern level variable child -> UnifiedPattern variable child
asUnifiedPattern = UnifiedPattern . asUnified . Rotate31

transformUnifiedPattern
    :: (forall level . MetaOrObject level => Pattern level variable a -> b)
    -> (UnifiedPattern variable a -> b)
transformUnifiedPattern f =
    transformUnified (f . unRotate31) . getUnifiedPattern

transformUnifiedPatternM
    :: Monad m
    => (forall level . MetaOrObject level
        => m (Pattern level variable a) -> m b)
    -> (m (UnifiedPattern variable a) -> m b)
transformUnifiedPatternM f =
    transformUnifiedM (f . fmap unRotate31) . fmap getUnifiedPattern


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

type KorePattern variable = (Fix (UnifiedPattern variable))

asKorePattern
    :: (MetaOrObject level)
    => Pattern level variable (KorePattern variable)
    -> KorePattern variable
asKorePattern = Fix . asUnifiedPattern

instance
    UnifiedPatternInterface UnifiedPattern
  where
    unifyPattern = asUnifiedPattern
    unifiedPatternApply = transformUnifiedPattern
    unifiedPatternApplyM = transformUnifiedPatternM

type CommonKorePattern = KorePattern Variable

applyKorePattern
    :: (Pattern Meta variable (KorePattern variable) -> b)
    -> (Pattern Object variable (KorePattern variable) -> b)
    -> (KorePattern variable -> b)
applyKorePattern metaT objectT korePattern =
    case getUnifiedPattern (unFix korePattern) of
        UnifiedMeta rp   -> metaT (unRotate31 rp)
        UnifiedObject rp -> objectT (unRotate31 rp)

type KoreAttributes = Attributes UnifiedPattern Variable

type KoreSentenceAlias level = SentenceAlias level UnifiedPattern Variable
type KoreSentenceSymbol level = SentenceSymbol level UnifiedPattern Variable
type KoreSentenceImport = SentenceImport UnifiedPattern Variable
type KoreSentenceAxiom = SentenceAxiom UnifiedSortVariable UnifiedPattern Variable
type KoreSentenceSort = SentenceSort Object UnifiedPattern Variable

newtype UnifiedSentence sortParam pat variable = UnifiedSentence
    { getUnifiedSentence :: Unified (Rotate41 Sentence sortParam pat variable) }

deriving instance
    ( Eq (pat variable (Fix (pat variable)))
    , Eq sortParam
    ) => Eq (UnifiedSentence sortParam pat variable)

deriving instance
    ( Show (pat variable (Fix (pat variable)))
    , Show sortParam
    ) => Show (UnifiedSentence sortParam pat variable)

type UnifiedSortVariable = Unified SortVariable
type UnifiedSort = Unified Sort

type KoreSentence = UnifiedSentence UnifiedSortVariable UnifiedPattern Variable

constructUnifiedSentence
    :: (MetaOrObject level)
    => (a -> Sentence level sortParam pat variable)
    -> (a -> UnifiedSentence sortParam pat variable)
constructUnifiedSentence ctor = UnifiedSentence . asUnified . Rotate41 . ctor

applyUnifiedSentence
    :: (Sentence Meta sortParam pat variable -> b)
    -> (Sentence Object sortParam pat variable -> b)
    -> (UnifiedSentence sortParam pat variable -> b)
applyUnifiedSentence metaT _ (UnifiedSentence (UnifiedMeta rs)) =
    metaT (unRotate41 rs)
applyUnifiedSentence _ objectT (UnifiedSentence (UnifiedObject rs)) =
    objectT (unRotate41 rs)

type KoreModule =
    Module UnifiedSentence UnifiedSortVariable UnifiedPattern Variable

type KoreDefinition =
    Definition UnifiedSentence UnifiedSortVariable UnifiedPattern Variable

instance
    ( MetaOrObject level
    ) => AsSentence KoreSentence (KoreSentenceAlias level)
  where
    asSentence = constructUnifiedSentence SentenceAliasSentence

instance
    ( MetaOrObject level
    ) => AsSentence KoreSentence (KoreSentenceSymbol level)
  where
    asSentence = constructUnifiedSentence SentenceSymbolSentence

instance AsSentence KoreSentence KoreSentenceImport where
    asSentence = constructUnifiedSentence SentenceImportSentence

instance AsSentence KoreSentence KoreSentenceAxiom where
    asSentence = constructUnifiedSentence SentenceAxiomSentence

instance AsSentence KoreSentence KoreSentenceSort where
    asSentence = constructUnifiedSentence SentenceSortSentence
