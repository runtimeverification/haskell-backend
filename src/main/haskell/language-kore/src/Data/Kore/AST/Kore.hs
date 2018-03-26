{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE StandaloneDeriving     #-}
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

import           Data.Hashable              (hash)
import           Data.Typeable              (Typeable)

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

instance Typeable v => UnifiedThing (UnifiedVariable v) v where
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
class UnifiedThing (p v) (PatternObjectMeta v (p v))
    => FixPattern v p
  where
    {-|'fixPatternApply' "lifts" a function defined on 'Pattern' to the
    domain of the fixed point 'p'.

    The resulting function unwraps the pattern from 'p' and maps it through
    the argument function.
    -}
    fixPatternApply
        :: (forall level . MetaOrObject level => Pattern level v (p v) -> b)
        -> (p v -> b)
    fixPatternApply f = transformUnified (f . getPatternObjectMeta)

data FixedPattern variable
    = MetaPattern !(Pattern Meta variable (FixedPattern variable))
    | ObjectPattern !(Pattern Object variable (FixedPattern variable))

newtype PatternObjectMeta v p a = PatternObjectMeta
    { getPatternObjectMeta :: Pattern a v p }

instance Typeable v
    => UnifiedThing (FixedPattern v) (PatternObjectMeta v (FixedPattern v))
  where
    destructor (MetaPattern p)   = Left (PatternObjectMeta p)
    destructor (ObjectPattern p) = Right (PatternObjectMeta p)
    metaConstructor = MetaPattern . getPatternObjectMeta
    objectConstructor = ObjectPattern . getPatternObjectMeta

asUnifiedPattern
    :: (MetaOrObject level, VariableClass variable)
    => Pattern level variable (FixedPattern variable) -> FixedPattern variable
asUnifiedPattern = asUnified . PatternObjectMeta

instance VariableClass variable => FixPattern variable FixedPattern where

{-|'UnifiedPattern' corresponds to the @pattern@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
type UnifiedPattern = FixedPattern Variable

deriving instance Eq UnifiedPattern
deriving instance Show UnifiedPattern

type KoreAttributes = Attributes FixedPattern Variable

type KoreSentenceAlias level = SentenceAlias level FixedPattern Variable
type KoreSentenceSymbol level = SentenceSymbol level FixedPattern Variable
type KoreSentenceImport = SentenceImport FixedPattern Variable
type KoreSentenceAxiom = SentenceAxiom UnifiedSortVariable FixedPattern Variable
type KoreSentenceSort = SentenceSort Object FixedPattern Variable

data UnifiedSentence sortParam pat variable
    = MetaSentence (Sentence Meta sortParam pat variable)
    | ObjectSentence (Sentence Object sortParam pat variable)

newtype
    Rotate31 t (pat :: (* -> *) -> *) (variable :: * -> *) level
  = Rotate31 { unRotate31 :: t level pat variable}
type LeveledSentenceAlias = Rotate31 SentenceAlias
type LeveledSentenceSymbol = Rotate31 SentenceSymbol

newtype
    Rotate41 t sortParam (pat :: (* -> *) -> *) (variable :: * -> *) level
  = Rotate41 { unRotate41 :: t level sortParam pat variable}
type LeveledSentence = Rotate41 Sentence

asKoreSymbolSentence
    :: MetaOrObject level => KoreSentenceSymbol level -> KoreSentence
asKoreSymbolSentence = asUnified . Rotate41 . SentenceSymbolSentence

asKoreAliasSentence
    :: MetaOrObject level => KoreSentenceAlias level -> KoreSentence
asKoreAliasSentence = asUnified . Rotate41 . SentenceAliasSentence

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

type KoreSentence = UnifiedSentence UnifiedSortVariable FixedPattern Variable
type KoreModule =
    Module UnifiedSentence UnifiedSortVariable FixedPattern Variable

type KoreDefinition =
    Definition UnifiedSentence UnifiedSortVariable FixedPattern Variable

instance AsSentence KoreSentence (KoreSentenceAlias Meta) where
    asSentence = MetaSentence . SentenceAliasSentence

instance AsSentence KoreSentence (KoreSentenceAlias Object) where
    asSentence = ObjectSentence . SentenceAliasSentence

instance AsSentence KoreSentence (KoreSentenceSymbol Meta) where
    asSentence = MetaSentence . SentenceSymbolSentence

instance AsSentence KoreSentence (KoreSentenceSymbol Object) where
    asSentence = ObjectSentence . SentenceSymbolSentence

instance AsSentence KoreSentence KoreSentenceImport where
    asSentence = MetaSentence . SentenceImportSentence

instance AsSentence KoreSentence KoreSentenceAxiom where
    asSentence = MetaSentence . SentenceAxiomSentence

instance AsSentence KoreSentence KoreSentenceSort where
    asSentence = ObjectSentence . SentenceSortSentence
