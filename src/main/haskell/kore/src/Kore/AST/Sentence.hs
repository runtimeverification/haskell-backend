{-|
Module      : Kore.AST.Sentence
Description : Data Structures for representing the Kore language AST that do not
              need unified constructs (see Kore.AST.Kore for the unified
              ones).
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that do not need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort Object' or 'Sort Meta')

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Kore.AST.Sentence
    ( SentenceSymbol (..)
    , Symbol (..)
    , groundSymbol
    , SentenceAlias (..)
    , Alias (..)
    , SentenceSymbolOrAlias (..)
    , SentenceImport (..)
    , ModuleName (..)
    , SentenceSort (..)
    , SentenceAxiom (..)
    , SentenceHook (..)
    , Sentence (..)
    , sentenceAttributes
    , eraseSentenceAnnotations
    , AsSentence (..)
    , Module (..)
    , getModuleNameForError
    , Definition (..)
    , PureSentenceSymbol
    , PureSentenceAlias
    , PureSentenceImport
    , PureSentenceAxiom
    , PureSentence
    , PureModule
    , PureDefinition
    , UnifiedSentence (..)
    , constructUnifiedSentence
    , applyUnifiedSentence
    , eraseUnifiedSentenceAnnotations
    , KoreSentenceSymbol
    , KoreSentenceAlias
    , KoreSentenceImport
    , KoreSentenceAxiom
    , KoreSentenceSort
    , KoreSentenceHook
    , KoreSentence
    , KoreModule
    , KoreDefinition
    , asKoreAxiomSentence
    , asKoreClaimSentence
    , VerifiedKoreSentenceSymbol
    , VerifiedKoreSentenceAlias
    , VerifiedKoreSentenceImport
    , VerifiedKoreSentenceAxiom
    , VerifiedKoreSentenceSort
    , VerifiedKoreSentenceHook
    , VerifiedKoreSentence
    , VerifiedKoreModule
    , VerifiedKoreDefinition
    , Attributes (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Default
import           Data.Hashable
                 ( Hashable (..) )
import           Data.Proxy
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Generics
                 ( Generic )

import qualified Kore.Annotation.Null as Annotation
import           Kore.AST.Kore as Kore
import           Kore.AST.Pure as Pure

{-|'Symbol' corresponds to the
@object-head-constructor{object-sort-variable-list}@ part of the
@object-symbol-declaration@ and @meta-symbol-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Symbol level = Symbol
    { symbolConstructor :: !(Id level)
    , symbolParams      :: ![SortVariable level]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Symbol level)

instance NFData (Symbol level)

-- |Given an 'Id', 'groundSymbol' produces the unparameterized 'Symbol'
-- corresponding to that argument.
groundSymbol :: Id level -> Symbol level
groundSymbol ctor = Symbol
    { symbolConstructor = ctor
    , symbolParams = []
    }

{-|'Alias' corresponds to the
@object-head-constructor{object-sort-variable-list}@ part of the
@object-alias-declaration@ and @meta-alias-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Alias level = Alias
    { aliasConstructor :: !(Id level)
    , aliasParams      :: ![SortVariable level]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Alias level)

instance NFData (Alias level)

{-|'Attributes' corresponds to the @attributes@ Kore syntactic declaration.
It is parameterized by the types of Patterns, @pat@.
-}

newtype Attributes =
    Attributes { getAttributes :: [CommonKorePattern] }
    deriving (Eq, Ord, Generic, Show)

instance Hashable Attributes

instance NFData Attributes

instance Default Attributes where
    def = Attributes []

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should implement 'MetaOrObject level'.
-}
data SentenceAlias (level :: *) (patternType :: *) =
    SentenceAlias
        { sentenceAliasAlias        :: !(Alias level)
        , sentenceAliasSorts        :: ![Sort level]
        , sentenceAliasResultSort   :: !(Sort level)
        , sentenceAliasLeftPattern  :: !(Application level (Variable level))
        , sentenceAliasRightPattern :: !patternType
        , sentenceAliasAttributes   :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable patternType => Hashable (SentenceAlias level patternType)

instance NFData patternType => NFData (SentenceAlias level patternType)

{-|'SentenceSymbol' corresponds to the @object-symbol-declaration@ and
@meta-symbol-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceSymbol (level :: *) (patternType :: *) =
    SentenceSymbol
        { sentenceSymbolSymbol     :: !(Symbol level)
        , sentenceSymbolSorts      :: ![Sort level]
        , sentenceSymbolResultSort :: !(Sort level)
        , sentenceSymbolAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceSymbol level patternType)

instance NFData (SentenceSymbol level patternType)

{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: Text }
    deriving (Eq, Generic, Ord, Show)

instance Hashable ModuleName

instance NFData ModuleName

getModuleNameForError :: ModuleName -> String
getModuleNameForError = Text.unpack . getModuleName

{-|'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
-- TODO (thomas.tuegel): Even though the parameters are unused, they must stay
-- to satisfy the functional dependencies on 'AsSentence' below. Because they
-- are phantom, every use of 'asSentence' for a 'SentenceImport' will require a
-- type ascription. We should refactor the class so this is not necessary and
-- remove the parameters.
data SentenceImport (patternType :: *) =
    SentenceImport
        { sentenceImportModuleName :: !ModuleName
        , sentenceImportAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceImport pat)

instance NFData (SentenceImport pat)

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort (level :: *) (patternType :: *) =
    SentenceSort
        { sentenceSortName       :: !(Id level)
        , sentenceSortParameters :: ![SortVariable level]
        , sentenceSortAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceSort level patternType)

instance NFData (SentenceSort level patternType)

{-|'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceAxiom (sortParam :: *) (patternType :: *) =
    SentenceAxiom
        { sentenceAxiomParameters :: ![sortParam]
        , sentenceAxiomPattern    :: !patternType
        , sentenceAxiomAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance
    (Hashable sortParam, Hashable patternType) =>
    Hashable (SentenceAxiom sortParam patternType)

instance
    (NFData sortParam, NFData patternType) =>
    NFData (SentenceAxiom sortParam patternType)

{-|@SentenceHook@ corresponds to @hook-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
Note that we are reusing the 'SentenceSort' and 'SentenceSymbol' structures to
represent hooked sorts and hooked symbols.
-}
data SentenceHook (patternType :: *) where
    SentenceHookedSort
        :: !(SentenceSort Object patternType) -> SentenceHook patternType
    SentenceHookedSymbol
        :: !(SentenceSymbol Object patternType) -> SentenceHook patternType
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceHook patternType)

instance NFData (SentenceHook patternType)

{-|The 'Sentence' type corresponds to the @declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The @symbol-declaration@ and @alias-declaration@ categories were also merged
into 'Sentence', using the @level@ parameter to distinguish the 'Meta' and
'Object' variants.
Since axioms and imports exist at both meta and kore levels, we use 'Meta'
to qualify them. In contrast, since sort declarations are not available
at the meta level, we qualify them with 'Object'.
-}
data Sentence (level :: *) (sortParam :: *) (patternType :: *) where
    SentenceAliasSentence
        :: !(SentenceAlias level patternType)
        -> Sentence level sortParam patternType
    SentenceSymbolSentence
        :: !(SentenceSymbol level patternType)
        -> Sentence level sortParam patternType
    SentenceImportSentence
        :: !(SentenceImport patternType)
        -> Sentence Meta sortParam patternType
    SentenceAxiomSentence
        :: !(SentenceAxiom sortParam patternType)
        -> Sentence Meta sortParam patternType
    SentenceClaimSentence
        :: !(SentenceAxiom sortParam patternType)
        -> Sentence Meta sortParam patternType
    SentenceSortSentence
        :: !(SentenceSort level patternType)
        -> Sentence level sortParam patternType
    SentenceHookSentence
        :: !(SentenceHook patternType)
        -> Sentence Object sortParam patternType

deriving instance
    (Eq sortParam, Eq patternType) =>
    Eq (Sentence level sortParam patternType)

deriving instance Foldable (Sentence level sortParam)

deriving instance Functor (Sentence level sortParam)

deriving instance
    (Ord sortParam, Ord patternType) =>
    Ord (Sentence level sortParam patternType)

deriving instance
    (Show sortParam, Show patternType) =>
    Show (Sentence level sortParam patternType)

deriving instance Traversable (Sentence level sortParam)

instance
    (NFData sortParam, NFData patternType) =>
    NFData (Sentence level sortParam patternType)
  where
    rnf =
        \case
            SentenceAliasSentence p -> rnf p
            SentenceSymbolSentence p -> rnf p
            SentenceImportSentence p -> rnf p
            SentenceAxiomSentence p -> rnf p
            SentenceClaimSentence p -> rnf p
            SentenceSortSentence p -> rnf p
            SentenceHookSentence p -> rnf p

{- | The attributes associated with a sentence.

Every sentence type has attributes, so this operation is total.

 -}
sentenceAttributes :: Sentence level sortParam patternType -> Attributes
sentenceAttributes =
    \case
        SentenceAliasSentence
            SentenceAlias { sentenceAliasAttributes } ->
                sentenceAliasAttributes
        SentenceSymbolSentence
            SentenceSymbol { sentenceSymbolAttributes } ->
                sentenceSymbolAttributes
        SentenceImportSentence
            SentenceImport { sentenceImportAttributes } ->
                sentenceImportAttributes
        SentenceAxiomSentence
            SentenceAxiom { sentenceAxiomAttributes } ->
                sentenceAxiomAttributes
        SentenceClaimSentence
            SentenceAxiom { sentenceAxiomAttributes } ->
                sentenceAxiomAttributes
        SentenceSortSentence
            SentenceSort { sentenceSortAttributes } ->
                sentenceSortAttributes
        SentenceHookSentence sentence ->
            case sentence of
                SentenceHookedSort
                    SentenceSort { sentenceSortAttributes } ->
                        sentenceSortAttributes
                SentenceHookedSymbol
                    SentenceSymbol { sentenceSymbolAttributes } ->
                        sentenceSymbolAttributes

-- | Erase the pattern annotations within a 'Sentence'.
eraseSentenceAnnotations
    :: Functor domain
    => Sentence
        level
        sortParam
        (PurePattern level domain variable erased)
    -> Sentence
        level
        sortParam
        (PurePattern level domain variable (Annotation.Null level))
eraseSentenceAnnotations sentence = (<$) Annotation.Null <$> sentence

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module (sentence :: *) =
    Module
        { moduleName       :: !ModuleName
        , moduleSentences  :: ![sentence]
        , moduleAttributes :: !Attributes
        }
    deriving (Eq, Functor, Foldable, Generic, Show, Traversable)

instance Hashable sentence => Hashable (Module sentence)

instance NFData sentence => NFData (Module sentence)

{-|Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition (sentence :: *) =
    Definition
        { definitionAttributes :: !Attributes
        , definitionModules    :: ![Module sentence]
        }
    deriving (Eq, Functor, Foldable, Generic, Show, Traversable)

instance Hashable sentence => Hashable (Definition sentence)

instance NFData sentence => NFData (Definition sentence)

class SentenceSymbolOrAlias (sentence :: * -> * -> *) where
    getSentenceSymbolOrAliasConstructor
        :: sentence level patternType -> Id level
    getSentenceSymbolOrAliasSortParams
        :: sentence level patternType -> [SortVariable level]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence level patternType -> [Sort level]
    getSentenceSymbolOrAliasResultSort
        :: sentence level patternType -> Sort level
    getSentenceSymbolOrAliasAttributes
        :: sentence level patternType -> Attributes
    getSentenceSymbolOrAliasSentenceName
        :: sentence level patternType -> String
    getSentenceSymbolOrAliasHead
        :: sentence level patternType
        -> [Sort level]
        -> SymbolOrAlias level
    getSentenceSymbolOrAliasHead sentence sortParameters = SymbolOrAlias
        { symbolOrAliasConstructor =
            getSentenceSymbolOrAliasConstructor sentence
        , symbolOrAliasParams = sortParameters
        }

instance SentenceSymbolOrAlias SentenceAlias where
    getSentenceSymbolOrAliasConstructor = aliasConstructor . sentenceAliasAlias
    getSentenceSymbolOrAliasSortParams = aliasParams . sentenceAliasAlias
    getSentenceSymbolOrAliasArgumentSorts = sentenceAliasSorts
    getSentenceSymbolOrAliasResultSort = sentenceAliasResultSort
    getSentenceSymbolOrAliasAttributes = sentenceAliasAttributes
    getSentenceSymbolOrAliasSentenceName _ = "alias"

instance SentenceSymbolOrAlias SentenceSymbol where
    getSentenceSymbolOrAliasConstructor =
        symbolConstructor . sentenceSymbolSymbol
    getSentenceSymbolOrAliasSortParams = symbolParams . sentenceSymbolSymbol
    getSentenceSymbolOrAliasArgumentSorts = sentenceSymbolSorts
    getSentenceSymbolOrAliasResultSort = sentenceSymbolResultSort
    getSentenceSymbolOrAliasAttributes = sentenceSymbolAttributes
    getSentenceSymbolOrAliasSentenceName _ = "symbol"

class AsSentence sentenceType s | s -> sentenceType where
    asSentence :: s -> sentenceType

-- |'KoreSentenceAlias' is the Kore ('Meta' and 'Object') version of
-- 'SentenceAlias'
type KoreSentenceAlias level = SentenceAlias level CommonKorePattern

type VerifiedKoreSentenceAlias level = SentenceAlias level VerifiedKorePattern

-- |'KoreSentenceSymbol' is the Kore ('Meta' and 'Object') version of
-- 'SentenceSymbol'
type KoreSentenceSymbol level = SentenceSymbol level CommonKorePattern

type VerifiedKoreSentenceSymbol level = SentenceSymbol level VerifiedKorePattern

-- |'KoreSentenceImport' is the Kore ('Meta' and 'Object') version of
-- 'SentenceImport'
type KoreSentenceImport = SentenceImport CommonKorePattern

type VerifiedKoreSentenceImport = SentenceImport VerifiedKorePattern

-- |'KoreSentenceAxiom' is the Kore ('Meta' and 'Object') version of
-- 'SentenceAxiom'
type KoreSentenceAxiom = SentenceAxiom UnifiedSortVariable CommonKorePattern

type VerifiedKoreSentenceAxiom =
    SentenceAxiom UnifiedSortVariable VerifiedKorePattern

-- |'KoreSentenceSort' is the Kore ('Meta' and 'Object') version of
-- 'SentenceSort'
type KoreSentenceSort level = SentenceSort level CommonKorePattern

type VerifiedKoreSentenceSort level = SentenceSort level VerifiedKorePattern

-- |'KoreSentenceHook' Kore ('Meta' and 'Object') version of
-- 'SentenceHook'
type KoreSentenceHook = SentenceHook CommonKorePattern

type VerifiedKoreSentenceHook = SentenceHook VerifiedKorePattern

{-|'UnifiedPattern' is joining the 'Meta' and 'Object' versions of 'Sentence',
to allow using toghether both 'Meta' and 'Object' sentences.
-}
data UnifiedSentence sortParam patternType where
    UnifiedMetaSentence
        :: !(Sentence Meta sortParam patternType)
        -> UnifiedSentence sortParam patternType

    UnifiedObjectSentence
        :: !(Sentence Object sortParam patternType)
        -> UnifiedSentence sortParam patternType
    deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance
    (NFData sortParam, NFData patternType) =>
    NFData (UnifiedSentence sortParam patternType)
  where
    rnf =
        \case
            UnifiedMetaSentence metaS -> rnf metaS
            UnifiedObjectSentence objectS -> rnf objectS

-- |'KoreSentence' instantiates 'UnifiedSentence' to describe sentences fully
-- corresponding to the @declaration@ syntactic category
-- from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
type KoreSentence = UnifiedSentence UnifiedSortVariable CommonKorePattern

type VerifiedKoreSentence =
    UnifiedSentence UnifiedSortVariable VerifiedKorePattern

type VerifiedKoreModule = Module VerifiedKoreSentence

type VerifiedKoreDefinition = Definition VerifiedKoreSentence

constructUnifiedSentence
    ::  forall a level sortParam patternType.
        MetaOrObject level
    => (a -> Sentence level sortParam patternType)
    -> (a -> UnifiedSentence sortParam patternType)
constructUnifiedSentence ctor =
    case isMetaOrObject (Proxy :: Proxy level) of
        IsMeta -> UnifiedMetaSentence . ctor
        IsObject -> UnifiedObjectSentence . ctor

-- |Given functions appliable to 'Meta' 'Sentence's and 'Object' 'Sentences's,
-- builds a combined function which can be applied on 'UnifiedSentence's.
applyUnifiedSentence
    :: (Sentence Meta sortParam patternType -> b)
    -> (Sentence Object sortParam patternType -> b)
    -> (UnifiedSentence sortParam patternType -> b)
applyUnifiedSentence metaT objectT =
    \case
        UnifiedMetaSentence metaS -> metaT metaS
        UnifiedObjectSentence objectS -> objectT objectS

-- | Erase the pattern annotations within a 'UnifiedSentence'.
eraseUnifiedSentenceAnnotations
    :: Functor domain
    => UnifiedSentence
        sortParam
        (KorePattern domain variable erased)
    -> UnifiedSentence
        sortParam
        (KorePattern domain variable (Unified Annotation.Null))
eraseUnifiedSentenceAnnotations sentence = Kore.eraseAnnotations <$> sentence

-- |'KoreModule' fully instantiates 'Module' to correspond to the second, third,
-- and forth non-terminals of the @definition@ syntactic category from the
-- Semantics of K, Section 9.1.6 (Declaration and Definitions).
type KoreModule = Module KoreSentence

type KoreDefinition = Definition KoreSentence

instance
    ( MetaOrObject level
    , sortParam ~ UnifiedSortVariable
    ) =>
    AsSentence
        (UnifiedSentence sortParam (KorePattern domain variable annotation))
        (SentenceAlias level (KorePattern domain variable annotation))
  where
    asSentence = constructUnifiedSentence SentenceAliasSentence

instance
    ( MetaOrObject level
    , sortParam ~ UnifiedSortVariable
    ) =>
    AsSentence
        (UnifiedSentence sortParam (KorePattern domain variable annotation))
        (SentenceSymbol level (KorePattern domain variable annotation))
  where
    asSentence = constructUnifiedSentence SentenceSymbolSentence

instance
    (sortParam ~ UnifiedSortVariable) =>
    AsSentence
        (UnifiedSentence sortParam (KorePattern domain variable annotation))
        (SentenceImport (KorePattern domain variable annotation))
  where
    asSentence = constructUnifiedSentence SentenceImportSentence

asKoreAxiomSentence
    :: SentenceAxiom
        UnifiedSortVariable
        (KorePattern domain variable annotation)
    -> UnifiedSentence
        UnifiedSortVariable
        (KorePattern domain variable annotation)
asKoreAxiomSentence = constructUnifiedSentence SentenceAxiomSentence

asKoreClaimSentence
    :: SentenceAxiom
        UnifiedSortVariable
        (KorePattern domain variable annotation)
    -> UnifiedSentence
        UnifiedSortVariable
        (KorePattern domain variable annotation)
asKoreClaimSentence = constructUnifiedSentence SentenceClaimSentence

instance
    ( MetaOrObject level
    , sortParam ~ UnifiedSortVariable
    ) =>
    AsSentence
        (UnifiedSentence sortParam (KorePattern domain variable annotation))
        (SentenceSort level (KorePattern domain variable annotation))
  where
    asSentence = constructUnifiedSentence SentenceSortSentence


instance
    (sortParam ~ UnifiedSortVariable) =>
    AsSentence
        (UnifiedSentence sortParam (KorePattern domain variable annotation))
        (SentenceHook (KorePattern domain variable annotation))
  where
    asSentence = constructUnifiedSentence SentenceHookSentence

-- |'PureSentenceAxiom' is the pure (fixed-@level@) version of 'SentenceAxiom'
type PureSentenceAxiom level domain =
    SentenceAxiom (SortVariable level) (CommonPurePattern level domain)

-- |'PureSentenceAlias' is the pure (fixed-@level@) version of 'SentenceAlias'
type PureSentenceAlias level domain =
    SentenceAlias level (CommonPurePattern level domain)

-- |'PureSentenceSymbol' is the pure (fixed-@level@) version of 'SentenceSymbol'
type PureSentenceSymbol level domain =
    SentenceSymbol level (CommonPurePattern level domain)

-- |'PureSentenceImport' is the pure (fixed-@level@) version of 'SentenceImport'
type PureSentenceImport level domain =
    SentenceImport (CommonPurePattern level domain)

-- |'PureSentence' is the pure (fixed-@level@) version of 'Sentence'
type PureSentence level domain =
    Sentence level (SortVariable level) (CommonPurePattern level domain)

instance
    ( MetaOrObject level
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence
            level
            sortParam
            (PurePattern level domain variable annotation)
        )
        (SentenceAlias level (PurePattern level domain variable annotation))
  where
    asSentence = SentenceAliasSentence

instance
    ( MetaOrObject level
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence
            level
            sortParam
            (PurePattern level domain variable annotation)
        )
        (SentenceSymbol level (PurePattern level domain variable annotation))
  where
    asSentence = SentenceSymbolSentence

instance
    ( sortParam ~ SortVariable level
    , level ~ Meta
    ) =>
    AsSentence
        (Sentence
            level
            sortParam
            (PurePattern level domain variable annotation)
        )
        (SentenceImport (PurePattern level domain variable annotation))
  where
    asSentence = SentenceImportSentence

instance
    ( level ~ Meta
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence
            level
            sortParam
            (PurePattern level domain variable annotation)
        )
        (SentenceAxiom sortParam (PurePattern level domain variable annotation))
  where
    asSentence = SentenceAxiomSentence

instance
    ( MetaOrObject level
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence
            level
            sortParam
            (PurePattern level domain variable annotation)
        )
        (SentenceSort level (PurePattern level domain variable annotation))
  where
    asSentence = SentenceSortSentence


instance
    ( level ~ Object
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence
            level
            sortParam
            (PurePattern level domain variable annotation)
        )
        (SentenceHook (PurePattern level domain variable annotation))
  where
    asSentence = SentenceHookSentence

-- |'PureModule' is the pure (fixed-@level@) version of 'Module'
type PureModule level domain = Module (PureSentence level domain)

-- |'PureDefinition' is the pure (fixed-@level@) version of 'Definition'
type PureDefinition level domain = Definition (PureSentence level domain)
