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
module Kore.AST.Sentence where

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

import           Data.Functor.Foldable.Orphans ()
import           Kore.AST.Kore
import           Kore.AST.Pure
import qualified Kore.Domain.Builtin as Domain

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

instance NFData Attributes

instance Default Attributes where
    def = Attributes []

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceAlias
    (level :: *)
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (domain :: * -> *)
    (variable :: * -> *)
  = SentenceAlias
    { sentenceAliasAlias        :: !(Alias level)
    , sentenceAliasSorts        :: ![Sort level]
    , sentenceAliasResultSort   :: !(Sort level)
    , sentenceAliasLeftPattern
        :: !(Pattern level domain variable (pat domain variable ()))
    , sentenceAliasRightPattern
        :: !(Pattern level domain variable (pat domain variable ()))
    , sentenceAliasAttributes   :: !Attributes
    }
  deriving (Generic)

deriving instance
    ( Eq (Pattern level domain variable child)
    , child ~ pat domain variable ()
    ) =>
    Eq (SentenceAlias level pat domain variable)

deriving instance
    ( Ord (Pattern level domain variable child)
    , child ~ pat domain variable ()
    ) =>
    Ord (SentenceAlias level pat domain variable)

deriving instance
    ( Show (Pattern level domain variable child)
    , child ~ pat domain variable ()
    ) =>
    Show (SentenceAlias level pat domain variable)

instance
    ( NFData (Pattern level domain variable child)
    , NFData (variable level)
    , child ~ pat domain variable ()
    ) => NFData (SentenceAlias level pat domain variable)

{-|'SentenceSymbol' corresponds to the @object-symbol-declaration@ and
@meta-symbol-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceSymbol
    (level :: *)
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (domain :: * -> *)
    (variable :: * -> *)
  = SentenceSymbol
    { sentenceSymbolSymbol     :: !(Symbol level)
    , sentenceSymbolSorts      :: ![Sort level]
    , sentenceSymbolResultSort :: !(Sort level)
    , sentenceSymbolAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance NFData (SentenceSymbol level pat domain variable)

{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: Text }
    deriving (Eq, Generic, Ord, Show)

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
data SentenceImport
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (domain :: * -> *)
    (variable :: * -> *)
  = SentenceImport
    { sentenceImportModuleName :: !ModuleName
    , sentenceImportAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance NFData (SentenceImport pat domain variable)

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort
    (level :: *)
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (domain :: * -> *)
    (variable :: * -> *)
  = SentenceSort
    { sentenceSortName       :: !(Id level)
    , sentenceSortParameters :: ![SortVariable level]
    , sentenceSortAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance NFData (SentenceSort level pat domain variable)

{-|'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceAxiom
    (param :: *)
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (dom :: * -> *)
    (var :: * -> *)
  = SentenceAxiom
    { sentenceAxiomParameters :: ![param]
    , sentenceAxiomPattern    :: !(pat dom var ())
    , sentenceAxiomAttributes :: !Attributes
    }
  deriving (Generic)

deriving instance
    ( Eq param
    , Eq (pat dom var ())
    ) =>
    Eq (SentenceAxiom param pat dom var)

deriving instance
    ( Ord param
    , Ord (pat dom var ())
    ) =>
    Ord (SentenceAxiom param pat dom var)

deriving instance
    ( Show param
    , Show (pat dom var ())
    ) =>
    Show (SentenceAxiom param pat dom var)

instance
    ( NFData param
    , NFData (pat dom var ())
    ) =>
    NFData (SentenceAxiom param pat dom var)

{-|@SentenceHook@ corresponds to @hook-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
Note that we are reusing the 'SentenceSort' and 'SentenceSymbol' structures to
represent hooked sorts and hooked symbols.
-}
data SentenceHook
    (level :: *)
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (domain :: * -> *)
    (variable :: * -> *)
  = SentenceHookedSort !(SentenceSort level pat domain variable)
  | SentenceHookedSymbol !(SentenceSymbol level pat domain variable)
    deriving (Eq, Generic, Show)

instance NFData (SentenceHook level pat domain variable)

{-|The 'Sentence' type corresponds to the @declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The @symbol-declaration@ and @alias-declaration@ categories were also merged
into 'Sentence', using the @level@ parameter to distinguish the 'Meta' and
'Object' variants.
Since axioms and imports exist at both meta and kore levels, we use 'Meta'
to qualify them. In contrast, since sort declarations are not available
at the meta level, we qualify them with 'Object'.
-}
data Sentence
    (level :: *)
    (param :: *)
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (domain :: * -> *)
    (variable :: * -> *)
  where
    SentenceAliasSentence
        :: !(SentenceAlias level pat domain variable)
        -> Sentence level param pat domain variable
    SentenceSymbolSentence
        :: !(SentenceSymbol level pat domain variable)
        -> Sentence level param pat domain variable
    SentenceImportSentence
        :: !(SentenceImport pat domain variable)
        -> Sentence Meta param pat domain variable
    SentenceAxiomSentence
        :: !(SentenceAxiom param pat domain variable)
        -> Sentence Meta param pat domain variable
    SentenceClaimSentence
        :: !(SentenceAxiom param pat domain variable)
        -> Sentence Meta param pat domain variable
    SentenceSortSentence
        :: !(SentenceSort level pat domain variable)
        -> Sentence level param pat domain variable
    SentenceHookSentence
        :: !(SentenceHook Object pat domain variable)
        -> Sentence Object param pat domain variable

deriving instance
    ( Eq (SentenceAlias level pat domain variable)
    , Eq (SentenceSymbol level pat domain variable)
    , Eq (SentenceImport pat domain variable)
    , Eq (SentenceAxiom param pat domain variable)
    , Eq (SentenceSort level pat domain variable)
    , Eq (SentenceHook level pat domain variable)
    ) => Eq (Sentence level param pat domain variable)

deriving instance
    ( Ord (SentenceAlias level pat domain variable)
    , Ord (SentenceSymbol level pat domain variable)
    , Ord (SentenceImport pat domain variable)
    , Ord (SentenceAxiom param pat domain variable)
    , Ord (SentenceSort level pat domain variable)
    , Ord (SentenceHook level pat domain variable)
    ) => Ord (Sentence level param pat domain variable)

deriving instance
    ( Show (SentenceAlias level pat domain variable)
    , Show (SentenceSymbol level pat domain variable)
    , Show (SentenceImport pat domain variable)
    , Show (SentenceAxiom param pat domain variable)
    , Show (SentenceSort level pat domain variable)
    , Show (SentenceHook level pat domain variable)
    ) => Show (Sentence level param pat domain variable)

instance
    ( NFData (SentenceAlias level pat domain variable)
    , NFData (SentenceSymbol level pat domain variable)
    , NFData (SentenceImport pat domain variable)
    , NFData (SentenceAxiom param pat domain variable)
    , NFData (SentenceSort level pat domain variable)
    , NFData (SentenceHook level pat domain variable)
    ) =>
    NFData (Sentence level param pat domain variable)
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
sentenceAttributes :: Sentence level param pat domain variable -> Attributes
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

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module
    sentence
    param
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (domain :: * -> *)
    (variable :: * -> *)
  = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![sentence param pat domain variable]
    , moduleAttributes :: !Attributes
    }
  deriving (Eq, Generic, Show)

instance
    NFData (sentence param pat domain variable) =>
    NFData (Module sentence param pat domain variable)

{-|Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition
    sentence
    param
    (pat :: (* -> *) -> (* -> *) -> * -> *)
    (domain :: * -> *)
    (variable :: * -> *)
  = Definition
    { definitionAttributes :: !Attributes
    , definitionModules    :: ![Module sentence param pat domain variable]
    }
  deriving (Eq, Generic, Show)

instance
    NFData (sentence param pat domain variable) =>
    NFData (Definition sentence param pat domain variable)

class SentenceSymbolOrAlias
    (sentence
        :: *  -- sort parameter
        -> ((* -> *) -> (* -> *) -> * -> *)  -- pattern head
        -> (* -> *)  -- domain
        -> (* -> *)  -- variable
        -> *
    )
  where
    getSentenceSymbolOrAliasConstructor
        :: sentence level pat domain variable -> Id level
    getSentenceSymbolOrAliasSortParams
        :: sentence level pat domain variable -> [SortVariable level]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence level pat domain variable -> [Sort level]
    getSentenceSymbolOrAliasResultSort
        :: sentence level pat domain variable -> Sort level
    getSentenceSymbolOrAliasAttributes
        :: sentence level pat domain variable -> Attributes
    getSentenceSymbolOrAliasSentenceName
        :: sentence level pat domain variable -> String
    getSentenceSymbolOrAliasHead
        :: sentence level pat domain variable
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
type KoreSentenceAlias level =
    SentenceAlias level KorePattern Domain.Builtin Variable

-- |'KoreSentenceSymbol' is the Kore ('Meta' and 'Object') version of
-- 'SentenceSymbol'
type KoreSentenceSymbol level =
    SentenceSymbol level KorePattern Domain.Builtin Variable

-- |'KoreSentenceImport' is the Kore ('Meta' and 'Object') version of
-- 'SentenceImport'
type KoreSentenceImport =
    SentenceImport KorePattern Domain.Builtin Variable

-- |'KoreSentenceAxiom' is the Kore ('Meta' and 'Object') version of
-- 'SentenceAxiom'
type KoreSentenceAxiom =
    SentenceAxiom UnifiedSortVariable KorePattern Domain.Builtin Variable

-- |'KoreSentenceSort' is the Kore ('Meta' and 'Object') version of
-- 'SentenceSort'
type KoreSentenceSort level =
    SentenceSort level KorePattern Domain.Builtin Variable

-- |'KoreSentenceHook' Kore ('Meta' and 'Object') version of
-- 'SentenceHook'
type KoreSentenceHook =
    SentenceHook Object KorePattern Domain.Builtin Variable

{-|'UnifiedPattern' is joining the 'Meta' and 'Object' versions of 'Sentence',
to allow using toghether both 'Meta' and 'Object' sentences.
-}
data UnifiedSentence param pat domain variable where
    UnifiedMetaSentence
        :: !(Sentence Meta param pat domain var)
        -> UnifiedSentence param pat domain var

    UnifiedObjectSentence
        :: !(Sentence Object param pat domain var)
        -> UnifiedSentence param pat domain var

deriving instance
    ( Eq (Sentence Meta param pat domain variable)
    , Eq (Sentence Object param pat domain variable)
    ) => Eq (UnifiedSentence param pat domain variable)

deriving instance
    ( Ord (Sentence Meta param pat domain variable)
    , Ord (Sentence Object param pat domain variable)
    ) => Ord (UnifiedSentence param pat domain variable)

deriving instance
    ( Show (Sentence Meta param pat domain variable)
    , Show (Sentence Object param pat domain variable)
    ) => Show (UnifiedSentence param pat domain variable)

instance
    ( NFData (Sentence Meta param pat domain variable)
    , NFData (Sentence Object param pat domain variable)
    ) => NFData (UnifiedSentence param pat domain variable)
  where
    rnf =
        \case
            UnifiedMetaSentence metaS -> rnf metaS
            UnifiedObjectSentence objectS -> rnf objectS

-- |'KoreSentence' instantiates 'UnifiedSentence' to describe sentences fully
-- corresponding to the @declaration@ syntactic category
-- from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
type KoreSentence =
    UnifiedSentence UnifiedSortVariable KorePattern Domain.Builtin Variable

constructUnifiedSentence
    ::  forall a level param pat domain variable.
        MetaOrObject level
    => (a -> Sentence level param pat domain variable)
    -> (a -> UnifiedSentence param pat domain variable)
constructUnifiedSentence ctor =
    case isMetaOrObject (Proxy :: Proxy level) of
        IsMeta -> UnifiedMetaSentence . ctor
        IsObject -> UnifiedObjectSentence . ctor

-- |Given functions appliable to 'Meta' 'Sentence's and 'Object' 'Sentences's,
-- builds a combined function which can be applied on 'UnifiedSentence's.
applyUnifiedSentence
    :: (Sentence Meta param pat domain variable -> b)
    -> (Sentence Object param pat domain variable -> b)
    -> (UnifiedSentence param pat domain variable -> b)
applyUnifiedSentence metaT objectT =
    \case
        UnifiedMetaSentence metaS -> metaT metaS
        UnifiedObjectSentence objectS -> objectT objectS

-- |'KoreModule' fully instantiates 'Module' to correspond to the second, third,
-- and forth non-terminals of the @definition@ syntactic category from the
-- Semantics of K, Section 9.1.6 (Declaration and Definitions).
type KoreModule =
    Module
        UnifiedSentence
        UnifiedSortVariable
        KorePattern
        Domain.Builtin
        Variable

type KoreDefinition =
    Definition
        UnifiedSentence
        UnifiedSortVariable
        KorePattern
        Domain.Builtin
        Variable

instance
    ( MetaOrObject level
    , param ~ UnifiedSortVariable
    ) =>
    AsSentence
        (UnifiedSentence param KorePattern domain variable)
        (SentenceAlias level KorePattern domain variable)
  where
    asSentence = constructUnifiedSentence SentenceAliasSentence

instance
    ( MetaOrObject level
    , param ~ UnifiedSortVariable
    ) =>
    AsSentence
        (UnifiedSentence param KorePattern domain variable)
        (SentenceSymbol level KorePattern domain variable)
  where
    asSentence = constructUnifiedSentence SentenceSymbolSentence

instance
    (param ~ UnifiedSortVariable) =>
    AsSentence
        (UnifiedSentence param KorePattern domain variable)
        (SentenceImport KorePattern domain variable)
  where
    asSentence = constructUnifiedSentence SentenceImportSentence

instance
    (param ~ UnifiedSortVariable) =>
    AsSentence
        (UnifiedSentence param KorePattern domain variable)
        (SentenceAxiom param KorePattern domain variable)
  where
    asSentence = constructUnifiedSentence SentenceAxiomSentence

instance
    ( MetaOrObject level
    , param ~ UnifiedSortVariable
    ) =>
    AsSentence
        (UnifiedSentence param KorePattern domain variable)
        (SentenceSort level KorePattern domain variable)
  where
    asSentence = constructUnifiedSentence SentenceSortSentence


instance
    (param ~ UnifiedSortVariable) =>
    AsSentence
        (UnifiedSentence param KorePattern domain variable)
        (SentenceHook Object KorePattern domain variable)
  where
    asSentence = constructUnifiedSentence SentenceHookSentence

-- |'PureSentenceAxiom' is the pure (fixed-@level@) version of 'SentenceAxiom'
type PureSentenceAxiom level domain =
    SentenceAxiom (SortVariable level) (PurePattern level) domain Variable

-- |'PureSentenceAlias' is the pure (fixed-@level@) version of 'SentenceAlias'
type PureSentenceAlias level domain =
    SentenceAlias level (PurePattern level) domain Variable

-- |'PureSentenceSymbol' is the pure (fixed-@level@) version of 'SentenceSymbol'
type PureSentenceSymbol level domain =
    SentenceSymbol level (PurePattern level) domain Variable

-- |'PureSentenceImport' is the pure (fixed-@level@) version of 'SentenceImport'
type PureSentenceImport level domain =
    SentenceImport (PurePattern level) domain Variable

-- |'PureSentence' is the pure (fixed-@level@) version of 'Sentence'
type PureSentence level domain =
    Sentence level (SortVariable level) (PurePattern level) domain Variable

instance
    ( MetaOrObject level
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence level sortParam (PurePattern level) domain variable)
        (SentenceAlias level (PurePattern level) domain variable)
  where
    asSentence = SentenceAliasSentence

instance
    ( MetaOrObject level
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence level sortParam (PurePattern level) domain variable)
        (SentenceSymbol level (PurePattern level) domain variable)
  where
    asSentence = SentenceSymbolSentence

instance
    ( sortParam ~ SortVariable level
    , level ~ Meta
    ) =>
    AsSentence
        (Sentence level sortParam (PurePattern level) domain variable)
        (SentenceImport (PurePattern level) domain variable)
  where
    asSentence = SentenceImportSentence

instance
    ( level ~ Meta
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence level sortParam (PurePattern level) domain variable)
        (SentenceAxiom sortParam (PurePattern level) domain variable)
  where
    asSentence = SentenceAxiomSentence

instance
    ( MetaOrObject level
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence level sortParam (PurePattern level) domain variable)
        (SentenceSort level (PurePattern level) domain variable)
  where
    asSentence = SentenceSortSentence


instance
    ( level ~ Object
    , sortParam ~ SortVariable level
    ) =>
    AsSentence
        (Sentence level sortParam (PurePattern level) domain variable)
        (SentenceHook level (PurePattern level) domain variable)
  where
    asSentence = SentenceHookSentence

-- |'PureModule' is the pure (fixed-@level@) version of 'Module'
type PureModule level domain =
    Module
        (Sentence level)
        (SortVariable level)
        (PurePattern level)
        domain
        Variable

-- |'PureDefinition' is the pure (fixed-@level@) version of 'Definition'
type PureDefinition level domain =
    Definition
        (Sentence level)
        (SortVariable level)
        (PurePattern level)
        domain
        Variable
