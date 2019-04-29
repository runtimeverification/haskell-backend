{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that do not need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort' or 'Sort')

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
    , PureSentenceHook
    , PureSentence
    , PureModule
    , PureDefinition
    , castDefinitionDomainValues
    , ParsedSentenceAlias
    , ParsedSentenceSymbol
    , ParsedSentenceImport
    , ParsedSentenceAxiom
    , ParsedSentenceSort
    , ParsedSentenceHook
    , ParsedSentence
    , ParsedModule
    , ParsedDefinition
    , Attributes (..)
    ) where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Functor.Const
                 ( Const )
import           Data.Hashable
                 ( Hashable (..) )
import           Data.Maybe
                 ( catMaybes )
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Generic )

import qualified Kore.Annotation.Null as Annotation
import           Kore.AST.Pure as Pure
import           Kore.Attribute.Attributes
import qualified Kore.Domain.Builtin as Domain
import           Kore.Unparser

{-|'Symbol' corresponds to the
@object-head-constructor{object-sort-variable-list}@ part of the
@object-symbol-declaration@ and @meta-symbol-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Symbol level = Symbol
    { symbolConstructor :: !Id
    , symbolParams      :: ![SortVariable]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Symbol level)

instance NFData (Symbol level)

instance Unparse (Symbol level) where
    unparse Symbol { symbolConstructor, symbolParams } =
        unparse symbolConstructor
        <> parameters symbolParams

    unparse2 Symbol { symbolConstructor } =
        unparse2 symbolConstructor


-- |Given an 'Id', 'groundSymbol' produces the unparameterized 'Symbol'
-- corresponding to that argument.
groundSymbol :: Id -> Symbol level
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
    { aliasConstructor :: !Id
    , aliasParams      :: ![SortVariable]
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Alias level)

instance NFData (Alias level)

instance Unparse (Alias level) where
    unparse Alias { aliasConstructor, aliasParams } =
        unparse aliasConstructor
        <> parameters aliasParams
    unparse2 Alias { aliasConstructor } =
        unparse2 aliasConstructor

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should implement 'MetaOrObject level'.
-}
data SentenceAlias (level :: *) (patternType :: *) =
    SentenceAlias
        { sentenceAliasAlias        :: !(Alias level)
        , sentenceAliasSorts        :: ![Sort]
        , sentenceAliasResultSort   :: !Sort
        , sentenceAliasLeftPattern  :: !(Application level (Variable level))
        , sentenceAliasRightPattern :: !patternType
        , sentenceAliasAttributes   :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable patternType => Hashable (SentenceAlias level patternType)

instance NFData patternType => NFData (SentenceAlias level patternType)

instance Unparse patternType => Unparse (SentenceAlias level patternType) where
    unparse
        SentenceAlias
            { sentenceAliasAlias
            , sentenceAliasSorts
            , sentenceAliasResultSort
            , sentenceAliasLeftPattern
            , sentenceAliasRightPattern
            , sentenceAliasAttributes
            }
      =
        Pretty.fillSep
            [ "alias"
            , unparse sentenceAliasAlias <> arguments sentenceAliasSorts
            , ":"
            , unparse sentenceAliasResultSort
            , "where"
            , unparse sentenceAliasLeftPattern
            , ":="
            , unparse sentenceAliasRightPattern
            , unparse sentenceAliasAttributes
            ]

    unparse2
        SentenceAlias
            { sentenceAliasAlias
            , sentenceAliasSorts
            , sentenceAliasResultSort
            , sentenceAliasLeftPattern
            , sentenceAliasRightPattern
            , sentenceAliasAttributes
            }
      =
        Pretty.fillSep
            [ "alias"
            , unparse2 sentenceAliasAlias <> arguments2 sentenceAliasSorts
            , ":"
            , unparse2 sentenceAliasResultSort
            , "where"
            , unparse2 sentenceAliasLeftPattern
            , ":="
            , unparse2 sentenceAliasRightPattern
            , unparse2 sentenceAliasAttributes
            ]

{-|'SentenceSymbol' corresponds to the @object-symbol-declaration@ and
@meta-symbol-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceSymbol (level :: *) (patternType :: *) =
    SentenceSymbol
        { sentenceSymbolSymbol     :: !(Symbol level)
        , sentenceSymbolSorts      :: ![Sort]
        , sentenceSymbolResultSort :: !Sort
        , sentenceSymbolAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceSymbol level patternType)

instance NFData (SentenceSymbol level patternType)

instance Unparse (SentenceSymbol level patternType) where
    unparse
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
      =
        Pretty.fillSep
            [ "symbol"
            , unparse sentenceSymbolSymbol <> arguments sentenceSymbolSorts
            , ":"
            , unparse sentenceSymbolResultSort
            , unparse sentenceSymbolAttributes
            ]

    unparse2
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            }
      = Pretty.vsep
            [ Pretty.fillSep [ "symbol", unparse2 sentenceSymbolSymbol ]
            , Pretty.fillSep [ "axiom \\forall s Sorts"
                             , Pretty.parens (Pretty.fillSep
                                   [ "\\subset"
                                   , Pretty.parens (Pretty.fillSep
                                       [ unparse2 sentenceSymbolSymbol
                                       , unparse2Inhabitant sentenceSymbolSorts
                                       ])
                                   , unparse2 sentenceSymbolResultSort
                                   ])
                             ]
            ]
          where unparse2Inhabitant ss =
                  case ss of
                      [] -> ""
                      (s : rest) ->
                        (Pretty.parens (Pretty.fillSep ["\\inh", unparse2 s]))
                        <> (unparse2Inhabitant rest)


{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: Text }
    deriving (Eq, Generic, IsString, Ord, Show)

instance Hashable ModuleName

instance NFData ModuleName

instance Unparse ModuleName where
    unparse = Pretty.pretty . getModuleName
    unparse2 = Pretty.pretty . getModuleName


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

instance Unparse (SentenceImport patternType) where
    unparse
        SentenceImport { sentenceImportModuleName, sentenceImportAttributes }
      =
        Pretty.fillSep
            [ "import", unparse sentenceImportModuleName
            , unparse sentenceImportAttributes
            ]

    unparse2
        SentenceImport { sentenceImportModuleName, sentenceImportAttributes }
      =
        Pretty.fillSep
            [ "import", unparse2 sentenceImportModuleName
            , unparse2 sentenceImportAttributes
            ]

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort (level :: *) (patternType :: *) =
    SentenceSort
        { sentenceSortName       :: !Id
        , sentenceSortParameters :: ![SortVariable]
        , sentenceSortAttributes :: !Attributes
        }
    deriving (Eq, Foldable, Functor, Generic, Ord, Show, Traversable)

instance Hashable (SentenceSort level patternType)

instance NFData (SentenceSort level patternType)

instance Unparse (SentenceSort level patternType) where
    unparse
        SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            , sentenceSortAttributes
            }
      =
        Pretty.fillSep
            [ "sort"
            , unparse sentenceSortName <> parameters sentenceSortParameters
            , unparse sentenceSortAttributes
            ]

    unparse2
        SentenceSort
            { sentenceSortName
            , sentenceSortParameters
            }
      = Pretty.vsep
            [ Pretty.fillSep ["symbol", unparse2 sentenceSortName, "[sort]"]
            , Pretty.fillSep ["axiom"
                             , "\\subset"
                             , Pretty.parens (Pretty.fillSep
                                [ unparse2 sentenceSortName
                                , printLbSortsRb (length sentenceSortParameters)
                                ])
                             , "Sorts"
                             ]
            ]
      where printLbSortsRb n =
              case n of
                  0 -> ""
                  m -> Pretty.fillSep["(\\inh Sorts)", printLbSortsRb (m - 1)]


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

instance
    (Unparse sortParam, Unparse patternType) =>
    Unparse (SentenceAxiom sortParam patternType)
  where
    unparse = unparseAxiom "axiom"
    unparse2 = unparseAxiom2 "axiom"


unparseAxiom
    ::  ( Unparse patternType
        , Unparse sortParam
        )
    => Pretty.Doc ann
    -> SentenceAxiom sortParam patternType
    -> Pretty.Doc ann
unparseAxiom
    label
    SentenceAxiom
        { sentenceAxiomParameters
        , sentenceAxiomPattern
        , sentenceAxiomAttributes
        }
  =
    Pretty.fillSep
        [ label
        , parameters sentenceAxiomParameters
        , unparse sentenceAxiomPattern
        , unparse sentenceAxiomAttributes
        ]

unparseAxiom2
    ::  ( Unparse patternType
        , Unparse sortParam
        )
    => Pretty.Doc ann
    -> SentenceAxiom sortParam patternType
    -> Pretty.Doc ann
unparseAxiom2
    label
    SentenceAxiom
        { sentenceAxiomPattern
        , sentenceAxiomAttributes
        }
  =
    Pretty.fillSep
        [ label
        , unparse2 sentenceAxiomPattern
        , unparse2 sentenceAxiomAttributes
        ]

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

instance Unparse (SentenceHook patternType) where
    unparse =
        \case
            SentenceHookedSort a -> "hooked-" <> unparse a
            SentenceHookedSymbol a -> "hooked-" <> unparse a

    unparse2 =
        \case
            SentenceHookedSort a -> "hooked-" <> unparse2 a
            SentenceHookedSymbol a -> "hooked-" <> unparse2 a

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

instance
    (Unparse sortParam, Unparse patternType) =>
    Unparse (Sentence level sortParam patternType)
  where
     unparse =
        \case
            SentenceAliasSentence s -> unparse s
            SentenceSymbolSentence s -> unparse s
            SentenceImportSentence s -> unparse s
            SentenceAxiomSentence s -> unparseAxiom "axiom" s
            SentenceClaimSentence s -> unparseAxiom "claim" s
            SentenceSortSentence s -> unparse s
            SentenceHookSentence s -> unparse s

     unparse2 =
        \case
            SentenceAliasSentence s -> unparse2 s
            SentenceSymbolSentence s -> unparse2 s
            SentenceImportSentence s -> unparse2 s
            SentenceAxiomSentence s -> unparseAxiom2 "axiom" s
            SentenceClaimSentence s -> unparseAxiom2 "claim" s
            SentenceSortSentence s -> unparse2 s
            SentenceHookSentence s -> unparse2 s

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

instance Unparse sentence => Unparse (Module sentence) where
    unparse
        Module { moduleName, moduleSentences, moduleAttributes }
      =
        (Pretty.vsep . catMaybes)
            [ Just ("module" Pretty.<+> unparse moduleName)
            , case moduleSentences of
                [] -> Nothing
                _ ->
                    (Just . Pretty.indent 4 . Pretty.vsep)
                        (unparse <$> moduleSentences)
            , Just "endmodule"
            , Just (unparse moduleAttributes)
            ]

    unparse2
        Module { moduleName, moduleSentences, moduleAttributes }
      =
        (Pretty.vsep . catMaybes)
            [ Just ("module" Pretty.<+> unparse2 moduleName)
            , case moduleSentences of
                [] -> Nothing
                _ ->
                    (Just . Pretty.indent 4 . Pretty.vsep)
                        (unparse2 <$> moduleSentences)
            , Just "endmodule"
            , Just (unparse2 moduleAttributes)
            ]

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

instance Unparse sentence => Unparse (Definition sentence) where
    unparse Definition { definitionAttributes, definitionModules } =
        Pretty.vsep
            (unparse definitionAttributes : map unparse definitionModules)

    unparse2 Definition { definitionAttributes, definitionModules } =
        Pretty.vsep
            (unparse2 definitionAttributes : map unparse2 definitionModules)

class SentenceSymbolOrAlias (sentence :: * -> * -> *) where
    getSentenceSymbolOrAliasConstructor
        :: sentence level patternType -> Id
    getSentenceSymbolOrAliasSortParams
        :: sentence level patternType -> [SortVariable]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence level patternType -> [Sort]
    getSentenceSymbolOrAliasResultSort
        :: sentence level patternType -> Sort
    getSentenceSymbolOrAliasAttributes
        :: sentence level patternType -> Attributes
    getSentenceSymbolOrAliasSentenceName
        :: sentence level patternType -> String
    getSentenceSymbolOrAliasHead
        :: sentence level patternType
        -> [Sort]
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

-- |'PureSentenceAxiom' is the pure (fixed-@level@) version of 'SentenceAxiom'
type PureSentenceAxiom level domain =
    SentenceAxiom SortVariable (ParsedPurePattern level domain)

-- |'PureSentenceAlias' is the pure (fixed-@level@) version of 'SentenceAlias'
type PureSentenceAlias level domain =
    SentenceAlias level (ParsedPurePattern level domain)

-- |'PureSentenceSymbol' is the pure (fixed-@level@) version of 'SentenceSymbol'
type PureSentenceSymbol level domain =
    SentenceSymbol level (ParsedPurePattern level domain)

-- |'PureSentenceImport' is the pure (fixed-@level@) version of 'SentenceImport'
type PureSentenceImport level domain =
    SentenceImport (ParsedPurePattern level domain)

-- | 'PureSentenceHook' is the pure (fixed-@level@) version of 'SentenceHook'.
type PureSentenceHook domain = SentenceHook (ParsedPurePattern Object domain)

-- |'PureSentence' is the pure (fixed-@level@) version of 'Sentence'
type PureSentence level domain =
    Sentence level SortVariable (ParsedPurePattern level domain)

instance
    ( MetaOrObject level
    , sortParam ~ SortVariable
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
    , sortParam ~ SortVariable
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
    ( sortParam ~ SortVariable
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
    , sortParam ~ SortVariable
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
    , sortParam ~ SortVariable
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
    , sortParam ~ SortVariable
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

type ParsedSentenceSort =
    SentenceSort Object (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceSymbol =
    SentenceSymbol Object (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceAlias =
    SentenceAlias Object (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceImport =
    SentenceImport (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceAxiom =
    SentenceAxiom
        SortVariable
        (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceHook =
    SentenceHook (ParsedPurePattern Object Domain.Builtin)

type ParsedSentence =
    Sentence
        Object
        SortVariable
        (ParsedPurePattern Object Domain.Builtin)

type ParsedModule = Module ParsedSentence

type ParsedDefinition = Definition ParsedSentence

castDefinitionDomainValues
    :: Functor domain
    => PureDefinition level (Const Void)
    -> PureDefinition level domain
castDefinitionDomainValues = (fmap . fmap) Pure.castVoidDomainValues
