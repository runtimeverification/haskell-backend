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
module Data.Kore.AST.Kore where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.HaskellExtensions (Rotate31 (..), Rotate41 (..))

import           Data.Fix
import           Data.Typeable               (Typeable)

{-
import           Data.Hashable               (hash)
class ( Ord (Unified var)
      , ShowMetaOrObject var
      , Typeable var
      ) => VariableClass var
  where
    -- |Retrieves the sort of the variable
    getVariableSort :: MetaOrObject level => var level -> Sort level
    -- |Computes a hash identifying the variable
    getVariableHash :: var level -> Int

instance VariableClass Variable where
    getVariableSort = variableSort
    getVariableHash = hash . getId . variableName
-}

type PatternObjectMeta = Rotate31 Pattern

{-|'UnifiedPattern' corresponds to the @pattern@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
newtype UnifiedPattern variable child = UnifiedPattern
    { getUnifiedPattern :: Unified (Rotate31 Pattern variable child) }

asUnifiedPattern
    :: (MetaOrObject level, Typeable variable, Typeable child)
    => Pattern level variable child -> UnifiedPattern variable child
asUnifiedPattern = UnifiedPattern . asUnified . Rotate31

deriving instance
    ( Eq child
    , EqMetaOrObject variable
    ) => Eq (UnifiedPattern variable child)

deriving instance
    ( Show child
    , ShowMetaOrObject variable
    ) => Show (UnifiedPattern variable child)

type FixedPattern = UnifiedPattern
type KorePattern variable = (Fix (UnifiedPattern variable))

asKorePattern
    :: (MetaOrObject level, Typeable variable)
    => Pattern level variable (KorePattern variable)
    -> KorePattern variable
asKorePattern = Fix . asUnifiedPattern

type CommonKorePattern = KorePattern Variable

type KoreAttributes = Attributes FixedPattern Variable

type KoreSentenceAlias level = SentenceAlias level FixedPattern Variable
type KoreSentenceSymbol level = SentenceSymbol level FixedPattern Variable
type KoreSentenceImport = SentenceImport FixedPattern Variable
type KoreSentenceAxiom = SentenceAxiom (Unified SortVariable) FixedPattern Variable
type KoreSentenceSort = SentenceSort Object FixedPattern Variable

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

type KoreSentence = UnifiedSentence UnifiedSortVariable FixedPattern Variable

asUnifiedSentence
    :: (MetaOrObject level, Typeable pat, Typeable variable, Typeable sortParam)
    => (a -> Sentence level sortParam pat variable)
    -> (a -> UnifiedSentence sortParam pat variable)
asUnifiedSentence ctor = UnifiedSentence . asUnified . Rotate41 . ctor

type KoreModule =
    Module UnifiedSentence UnifiedSortVariable FixedPattern Variable

type KoreDefinition =
    Definition UnifiedSentence UnifiedSortVariable FixedPattern Variable

instance
    ( MetaOrObject level
    ) => AsSentence KoreSentence (KoreSentenceAlias level)
  where
    asSentence = asUnifiedSentence SentenceAliasSentence

instance
    ( MetaOrObject level
    ) => AsSentence KoreSentence (KoreSentenceSymbol level)
  where
    asSentence = asUnifiedSentence SentenceSymbolSentence

instance AsSentence KoreSentence KoreSentenceImport where
    asSentence = asUnifiedSentence SentenceImportSentence

instance AsSentence KoreSentence KoreSentenceAxiom where
    asSentence = asUnifiedSentence SentenceAxiomSentence

instance AsSentence KoreSentence KoreSentenceSort where
    asSentence = asUnifiedSentence SentenceSortSentence
