{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE UndecidableInstances  #-}

module Data.Kore.AST.Kore where

import           Data.Kore.AST.Common

import           Data.Fix
import           Data.Typeable                          (Typeable, cast)

import           Data.Kore.Datastructures.EmptyTestable

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

data Unified sort
    = UnifiedObject !(sort Object)
    | UnifiedMeta !(sort Meta)

deriving instance (Eq (sort Object), Eq (sort Meta)) => Eq (Unified sort)
deriving instance (Ord (sort Object), Ord (sort Meta)) => Ord (Unified sort)
deriving instance (Show (sort Object), Show (sort Meta)) => Show (Unified sort)
deriving instance
    ( Typeable (sort Object)
    , Typeable (sort Meta)
    ) => Typeable (Unified sort)

applyUnified
    :: (forall level . MetaOrObject level => thing level -> b)
    -> (Unified thing -> b)
applyUnified f (UnifiedObject o) = f o
applyUnified f (UnifiedMeta o)   = f o

mapUnified
    :: (forall level . MetaOrObject level => thing1 level -> thing2 level)
    -> (Unified thing1 -> Unified thing2)
mapUnified f (UnifiedObject o) = UnifiedObject (f o)
mapUnified f (UnifiedMeta o)   = UnifiedMeta (f o)

sequenceUnified
    :: Applicative a
    => (forall level . MetaOrObject level => thing1 level -> a (thing2 level))
    -> (Unified thing1 -> a (Unified thing2))
sequenceUnified f (UnifiedObject o) = UnifiedObject <$> f o
sequenceUnified f (UnifiedMeta o)   = UnifiedMeta <$> f o

asUnified
    :: (MetaOrObject level, Typeable thing) => thing level -> Unified thing
asUnified x = applyMetaObjectFunction x MetaOrObjectTransformer
    { objectTransformer = UnifiedObject
    , metaTransformer = UnifiedMeta
    }

newtype PatternObjectMeta v p a = PatternObjectMeta
    { getPatternObjectMeta :: Pattern a v p }
  deriving (Typeable, Eq, Show)

newtype UnifiedPattern v p = UnifiedPattern
    { getUnifiedPattern :: Unified (PatternObjectMeta v p) }
  deriving (Typeable)

deriving instance Show child => Show (UnifiedPattern Variable child)
deriving instance Eq child => Eq (UnifiedPattern Variable child)

instance Functor (UnifiedPattern v) where
    fmap f =
        UnifiedPattern
        . mapUnified (PatternObjectMeta . fmap f . getPatternObjectMeta)
        . getUnifiedPattern

instance Foldable (UnifiedPattern v) where
    foldMap f =
        applyUnified (foldMap f . getPatternObjectMeta) . getUnifiedPattern

instance Traversable (UnifiedPattern v) where
    sequenceA =
        fmap UnifiedPattern
        . sequenceUnified
            (fmap PatternObjectMeta . sequenceA . getPatternObjectMeta)
        . getUnifiedPattern

type FixedUnifiedPattern v = Fix (UnifiedPattern v)

type KorePattern = FixedUnifiedPattern Variable

applyUnifiedPattern
    :: (forall level . MetaOrObject level
        => Pattern level variable child -> result
       )
    -> (UnifiedPattern variable child -> result)
applyUnifiedPattern f =
    applyUnified (f . getPatternObjectMeta) . getUnifiedPattern

applyKorePattern
    :: (forall level . MetaOrObject level
        => Pattern level variable (FixedUnifiedPattern variable) -> result
       )
    -> (FixedUnifiedPattern variable -> result)
applyKorePattern f = applyUnifiedPattern f . unFix

asKorePattern
    :: (MetaOrObject level, Typeable variable)
    => Pattern level variable (FixedUnifiedPattern variable)
    -> FixedUnifiedPattern variable
asKorePattern = Fix . UnifiedPattern . asUnified . PatternObjectMeta

asMetaPattern
    :: (Typeable variable)
    => Pattern Meta variable (FixedUnifiedPattern variable)
    -> FixedUnifiedPattern variable
asMetaPattern = Fix . UnifiedPattern . UnifiedMeta . PatternObjectMeta

asObjectPattern
    :: (Typeable variable)
    => Pattern Object variable (FixedUnifiedPattern variable)
    -> FixedUnifiedPattern variable
asObjectPattern = Fix . UnifiedPattern . UnifiedObject . PatternObjectMeta

newtype Attributes = Attributes { getAttributes :: [KorePattern] }
  deriving (Eq, Show)

instance EmptyTestable Attributes where
    isEmpty = null . getAttributes

type KoreSentenceAlias = SentenceAlias Attributes
type KoreSentenceSymbol = SentenceSymbol Attributes
type KoreSentenceImport = SentenceImport Attributes
type KoreSentenceAxiom =
    SentenceAxiom (Unified SortVariable) KorePattern Attributes
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
  deriving (Show, Eq)

asSentenceAliasSentence
    :: MetaOrObject level => KoreSentenceAlias level -> Sentence
asSentenceAliasSentence v =
    applyMetaObjectFunction v MetaOrObjectTransformer
        { objectTransformer = ObjectSentenceAliasSentence
        , metaTransformer = MetaSentenceAliasSentence
        }

asSentenceSymbolSentence
    :: MetaOrObject level => KoreSentenceSymbol level -> Sentence
asSentenceSymbolSentence v =
    applyMetaObjectFunction v MetaOrObjectTransformer
        { objectTransformer = ObjectSentenceSymbolSentence
        , metaTransformer = MetaSentenceSymbolSentence
        }

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
    (SentenceAxiom (Unified SortVariable) KorePattern Attributes)
  where
    asSentence = SentenceAxiomSentence

instance AsSentence (SentenceSort Attributes Object) where
    asSentence = SentenceSortSentence
