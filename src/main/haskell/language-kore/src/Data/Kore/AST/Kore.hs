{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE StandaloneDeriving     #-}
module Data.Kore.AST.Kore where

import           Data.Kore.AST.Common

import           Data.Hashable                          (hash)
import           Data.Typeable                          (Typeable, cast)

import           Data.Kore.Datastructures.EmptyTestable

{-|Class identifying a Kore level. It should only be implemented by the
'Object' and 'Meta' types, and should satisfy.

* @ isObject Object && not (isMeta Object) == True @
* @ not (isObject Meta) && isMeta Meta == True @
-}
class (Show level, Ord level, Eq level, Typeable level)
    => MetaOrObject level
  where
    isObject :: level -> Bool
    isMeta :: level -> Bool
    isObject = not . isMeta
    isMeta = not . isObject

instance MetaOrObject Meta where
    isMeta _ = True
instance MetaOrObject Object where
    isObject _ = True

applyMetaObjectFunction
    :: (Typeable thing, MetaOrObject level)
    => thing level -> (thing Object -> c) -> (thing Meta -> c) -> c
applyMetaObjectFunction x = applyMetaObjectFunctionCasted (cast x) (cast x)
applyMetaObjectFunctionCasted
    :: Maybe (thing Object)
    -> Maybe (thing Meta)
    -> (thing Object -> c)
    -> (thing Meta -> c)
    -> c
applyMetaObjectFunctionCasted (Just x) Nothing f _ = f x
applyMetaObjectFunctionCasted Nothing (Just x) _ f = f x
applyMetaObjectFunctionCasted _ _ _ _ =
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
    asUnified x = applyMetaObjectFunction x objectConstructor metaConstructor

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

'p' is the fiexd point wrapping pattern.

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

newtype Attributes = Attributes { getAttributes :: [UnifiedPattern] }
    deriving (Eq, Show)

instance EmptyTestable Attributes where
    isEmpty = null . getAttributes

type KoreSentenceAlias = SentenceAlias Attributes
type KoreSentenceSymbol = SentenceSymbol Attributes
type KoreSentenceImport = SentenceImport Attributes
type KoreSentenceAxiom =
    SentenceAxiom UnifiedSortVariable UnifiedPattern Attributes
type KoreSentenceSort = SentenceSort Attributes Object

{-|The 'Sentence' type corresponds to the @declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The @symbol-declaration@ and @alias-declaration@ categories were also merged
into 'Sentence', with distinct constructors for the @Meta@ and @Object@
variants.
-}
data Sentence
    = MetaSentenceAliasSentence !(KoreSentenceAlias Meta)
    | ObjectSentenceAliasSentence !(KoreSentenceAlias Object)
    | MetaSentenceSymbolSentence !(KoreSentenceSymbol Meta)
    | ObjectSentenceSymbolSentence !(KoreSentenceSymbol Object)
    | SentenceImportSentence !KoreSentenceImport
    | SentenceAxiomSentence !KoreSentenceAxiom
    | SentenceSortSentence !KoreSentenceSort
    deriving (Eq, Show)

asSentenceAliasSentence
    :: MetaOrObject level => KoreSentenceAlias level -> Sentence
asSentenceAliasSentence v =
    applyMetaObjectFunction
        v ObjectSentenceAliasSentence MetaSentenceAliasSentence

asSentenceSymbolSentence
    :: MetaOrObject level => KoreSentenceSymbol level -> Sentence
asSentenceSymbolSentence v =
    applyMetaObjectFunction
        v ObjectSentenceSymbolSentence MetaSentenceSymbolSentence

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![Sentence]
    , moduleAttributes :: !Attributes
    }
    deriving (Eq, Show)

{-|Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition = Definition
    { definitionAttributes :: !Attributes
    , definitionModules    :: ![Module]
    }
    deriving (Eq, Show)

class AsSentence s where
    asSentence :: s -> Sentence

instance AsSentence (SentenceAlias Attributes Meta) where
    asSentence = MetaSentenceAliasSentence

instance AsSentence (SentenceAlias Attributes Object) where
    asSentence = ObjectSentenceAliasSentence

instance AsSentence (SentenceSymbol Attributes Meta) where
    asSentence = MetaSentenceSymbolSentence

instance AsSentence (SentenceSymbol Attributes Object) where
    asSentence = ObjectSentenceSymbolSentence

instance AsSentence (SentenceImport Attributes) where
    asSentence = SentenceImportSentence

instance AsSentence
    (SentenceAxiom UnifiedSortVariable UnifiedPattern Attributes)
  where
    asSentence = SentenceAxiomSentence

instance AsSentence (SentenceSort Attributes Object) where
    asSentence = SentenceSortSentence
