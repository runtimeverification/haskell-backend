{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
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

import           Data.Hashable        (hash)
import           Data.Typeable        (Typeable, cast)

{-|Class identifying a Kore level. It should only be implemented by the
'Object' and 'Meta' types, and should verify:

* @ isObject Object && not (isMeta Object) @
* @ not (isObject Meta) && isMeta Meta @
-}
class (Show level, Ord level, Eq level, Typeable level)
    => MetaOrObject level
  where
    isObject :: level -> Bool
    isMeta :: level -> Bool
    isObject = not . isMeta
    isMeta = not . isObject
    {-# MINIMAL isObject | isMeta #-}

instance MetaOrObject Meta where
    isMeta _ = True
instance MetaOrObject Object where
    isObject _ = True

data MetaOrObjectTransformer thing result = MetaOrObjectTransformer
    { metaTransformer   :: thing Meta -> result
    , objectTransformer :: thing Object -> result
    }

applyMetaObjectFunction
    :: (Typeable thing, MetaOrObject level)
    => thing level -> MetaOrObjectTransformer thing c -> c
applyMetaObjectFunction x = applyMetaObjectFunctionCasted (cast x) (cast x)
applyMetaObjectFunctionCasted
    :: Maybe (thing Object)
    -> Maybe (thing Meta)
    -> MetaOrObjectTransformer thing c
    -> c
applyMetaObjectFunctionCasted (Just x) Nothing f = objectTransformer f x
applyMetaObjectFunctionCasted Nothing (Just x) f = metaTransformer f x
applyMetaObjectFunctionCasted _ _ _ =
    error "applyMetaObjectFunctionCasted: this should not happen!"

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

class Typeable thing
    => UnifiedThing unifiedThing thing | unifiedThing -> thing
  where
    destructor :: unifiedThing -> Either (thing Meta) (thing Object)
    objectConstructor :: thing Object -> unifiedThing
    metaConstructor :: thing Meta -> unifiedThing
    transformUnified
        :: (forall level . MetaOrObject level => thing level -> b)
        -> (unifiedThing -> b)
    transformUnified f unifiedStuff =
        case destructor unifiedStuff of
            Left x  -> f x
            Right x -> f x
    asUnified :: MetaOrObject level => thing level -> unifiedThing
    asUnified x = applyMetaObjectFunction x MetaOrObjectTransformer
        { objectTransformer = objectConstructor
        , metaTransformer = metaConstructor
        }

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
