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
import           Data.Kore.AST.Metadata
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.HaskellExtensions (Rotate41 (..))

import           Data.Hashable               (hash)
import           Data.Typeable               (Typeable)

data UnifiedSort
    = ObjectSort !(Sort Object)
    | MetaSort !(Sort Meta)
    deriving (Show, Eq)

class ( Ord (UnifiedVariable var)
      , Show (var Object), Show (var Meta)
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

{-|'UnifiedVariable' corresponds to the @variable@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
data UnifiedVariable variable
    = MetaVariable !(variable Meta)
    | ObjectVariable !(variable Object)

deriving instance Eq (UnifiedVariable Variable)
deriving instance Ord (UnifiedVariable Variable)
deriving instance Show (UnifiedVariable Variable)

instance UnifiedThing UnifiedSort Sort where
    destructor (MetaSort s)   = Left s
    destructor (ObjectSort s) = Right s
    metaConstructor = MetaSort
    objectConstructor = ObjectSort

instance UnifiedThing UnifiedSortVariable SortVariable where
    destructor (MetaSortVariable v)   = Left v
    destructor (ObjectSortVariable v) = Right v
    metaConstructor = MetaSortVariable
    objectConstructor = ObjectSortVariable

instance Typeable var => UnifiedThing (UnifiedVariable var) var where
    destructor (MetaVariable v)   = Left v
    destructor (ObjectVariable v) = Right v
    metaConstructor = MetaVariable
    objectConstructor = ObjectVariable

{-|'UnifiedSortVariable' corresponds to the @variable@ syntactic category
from the Semantics of K, Section 9.1.2 (Sorts).
-}
data UnifiedSortVariable
    = ObjectSortVariable !(SortVariable Object)
    | MetaSortVariable !(SortVariable Meta)
    deriving (Show, Eq, Ord)

{-|'FixPattern' class corresponds to "fixed point"-like representations
of the 'Pattern' class.

'p' is the fixed point wrapping pattern.

'v' is the type of variables.
-}
class UnifiedThing (pat var) (PatternObjectMeta var (pat var) metadata)
    => FixPattern var metadata pat
  where
    {-|'fixPatternApply' "lifts" a function defined on 'Pattern' to the
    domain of the fixed point 'pat'.

    The resulting function unwraps the pattern from 'pat' and maps it through
    the argument function.
    -}
    fixPatternApply
        :: (forall level
            . MetaOrObject level => Pattern level var metadata (pat var) -> b)
        -> (pat var -> b)
    fixPatternApply f = transformUnified (f . getPatternObjectMeta)

data FixedPattern metadata variable
    = MetaPattern !(Pattern Meta variable metadata (FixedPattern metadata variable))
    | ObjectPattern !(Pattern Object variable metadata (FixedPattern metadata variable))

newtype PatternObjectMeta variable child metadata level = PatternObjectMeta
    { getPatternObjectMeta :: Pattern level variable metadata child }

instance Typeable var
    => UnifiedThing
        (FixedPattern metadata var)
        (PatternObjectMeta var (FixedPattern metadata var) metadata)
  where
    destructor (MetaPattern p)   = Left (PatternObjectMeta p)
    destructor (ObjectPattern p) = Right (PatternObjectMeta p)
    metaConstructor = MetaPattern . getPatternObjectMeta
    objectConstructor = ObjectPattern . getPatternObjectMeta

asUnifiedPattern
    :: (MetaOrObject level, VariableClass variable)
    => Pattern level variable (FixedPattern variable) -> FixedPattern variable
asUnifiedPattern = asUnified . PatternObjectMeta

instance VariableClass variable => FixPattern variable metadata (FixedPattern metadata) where

{-|'UnifiedPattern' corresponds to the @pattern@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
type UnifiedPattern = FixedPattern Variable

deriving instance
    ( EqMetadata Object Variable (UnifiedPattern metadata) metadata
    , EqMetadata Meta Variable (UnifiedPattern metadata) metadata
    )
    => Eq (UnifiedPattern metadata)
deriving instance
    ( ShowMetadata Object Variable (UnifiedPattern metadata) metadata
    , ShowMetadata Meta Variable (UnifiedPattern metadata) metadata
    )
    => Show (UnifiedPattern metadata)

type KoreAttributes metadata = Attributes (FixedPattern metadata) Variable

type KoreSentenceAlias metadata level = SentenceAlias level (FixedPattern metadata) Variable
type KoreSentenceSymbol metadata level = SentenceSymbol level (FixedPattern metadata) Variable
type KoreSentenceImport metadata = SentenceImport (FixedPattern metadata) Variable
type KoreSentenceAxiom metadata = SentenceAxiom UnifiedSortVariable (FixedPattern metadata) Variable
type KoreSentenceSort metadata = SentenceSort Object (FixedPattern metadata) Variable

data UnifiedSentence sortParam pat variable
    = MetaSentence (Sentence Meta sortParam pat variable)
    | ObjectSentence (Sentence Object sortParam pat variable)
  deriving (Show, Eq)

type LeveledSentence = Rotate41 Sentence

instance
    ( Typeable sortParam
    , Typeable pat
    , Typeable variable
    ) => UnifiedThing
        (UnifiedSentence sortParam pat variable)
        (LeveledSentence sortParam pat variable)
  where
    destructor (MetaSentence s)   = Left (Rotate41 s)
    destructor (ObjectSentence s) = Right (Rotate41 s)
    objectConstructor = ObjectSentence . unRotate41
    metaConstructor = MetaSentence . unRotate41

asKoreSymbolSentence
    :: MetaOrObject level => KoreSentenceSymbol level -> KoreSentence
asKoreSymbolSentence = asUnified . Rotate41 . SentenceSymbolSentence

asKoreAliasSentence
    :: MetaOrObject level => KoreSentenceAlias level -> KoreSentence
asKoreAliasSentence = asUnified . Rotate41 . SentenceAliasSentence

type KoreSentence metadata = UnifiedSentence UnifiedSortVariable (FixedPattern metadata) Variable
type KoreModule metadata =
    Module UnifiedSentence UnifiedSortVariable (FixedPattern metadata) Variable

type KoreDefinition metadata =
    Definition UnifiedSentence UnifiedSortVariable (FixedPattern metadata) Variable

instance AsSentence (KoreSentence metadata) (KoreSentenceAlias metadata Meta) where
    asSentence = MetaSentence . SentenceAliasSentence

instance AsSentence (KoreSentence metadata) (KoreSentenceAlias metadata Object) where
    asSentence = ObjectSentence . SentenceAliasSentence

instance AsSentence (KoreSentence metadata) (KoreSentenceSymbol metadata Meta) where
    asSentence = MetaSentence . SentenceSymbolSentence

instance AsSentence (KoreSentence metadata) (KoreSentenceSymbol metadata Object) where
    asSentence = ObjectSentence . SentenceSymbolSentence

instance AsSentence (KoreSentence metadata) (KoreSentenceImport metadata) where
    asSentence = MetaSentence . SentenceImportSentence

instance AsSentence (KoreSentence metadata) (KoreSentenceAxiom metadata) where
    asSentence = MetaSentence . SentenceAxiomSentence

instance AsSentence (KoreSentence metadata) (KoreSentenceSort metadata) where
    asSentence = ObjectSentence . SentenceSortSentence
