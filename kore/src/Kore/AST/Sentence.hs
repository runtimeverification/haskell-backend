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
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Pure as Pure
import           Kore.Attribute.Attributes
import qualified Kore.Domain.Builtin as Domain
import           Kore.Syntax.Sentence
import           Kore.Unparser


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

class SentenceSymbolOrAlias (sentence :: * -> *) where
    getSentenceSymbolOrAliasConstructor
        :: sentence patternType -> Id
    getSentenceSymbolOrAliasSortParams
        :: sentence patternType -> [SortVariable]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence patternType -> [Sort]
    getSentenceSymbolOrAliasResultSort
        :: sentence patternType -> Sort
    getSentenceSymbolOrAliasAttributes
        :: sentence patternType -> Attributes
    getSentenceSymbolOrAliasSentenceName
        :: sentence patternType -> String
    getSentenceSymbolOrAliasHead
        :: sentence patternType
        -> [Sort]
        -> SymbolOrAlias
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
type PureSentenceAlias domain = SentenceAlias (ParsedPurePattern Object domain)

-- |'PureSentenceSymbol' is the pure (fixed-@level@) version of 'SentenceSymbol'
type PureSentenceSymbol domain =
    SentenceSymbol (ParsedPurePattern Object domain)

-- |'PureSentenceImport' is the pure (fixed-@level@) version of 'SentenceImport'
type PureSentenceImport level domain =
    SentenceImport (ParsedPurePattern level domain)

-- | 'PureSentenceHook' is the pure (fixed-@level@) version of 'SentenceHook'.
type PureSentenceHook domain = SentenceHook (ParsedPurePattern Object domain)

-- |'PureSentence' is the pure (fixed-@level@) version of 'Sentence'
type PureSentence domain =
    Sentence SortVariable (ParsedPurePattern Object domain)

instance
    sortParam ~ SortVariable =>
    AsSentence
        (Sentence
            sortParam
            (PurePattern Object domain variable annotation)
        )
        (SentenceAlias (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceAliasSentence

instance
    sortParam ~ SortVariable =>
    AsSentence
        (Sentence
            sortParam
            (PurePattern Object domain variable annotation)
        )
        (SentenceSymbol (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceSymbolSentence

instance
    sortParam ~ SortVariable =>
    AsSentence
        (Sentence
            sortParam
            (PurePattern Object domain variable annotation)
        )
        (SentenceImport (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceImportSentence

instance
    sortParam ~ SortVariable =>
    AsSentence
        (Sentence
            sortParam
            (PurePattern Object domain variable annotation)
        )
        (SentenceAxiom sortParam (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceAxiomSentence

instance
    AsSentence
        (Sentence
            SortVariable
            (PurePattern Object domain variable annotation)
        )
        (SentenceSort (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceSortSentence


instance
    sortParam ~ SortVariable =>
    AsSentence
        (Sentence
            sortParam
            (PurePattern Object domain variable annotation)
        )
        (SentenceHook (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceHookSentence

-- |'PureModule' is the pure (fixed-@level@) version of 'Module'
type PureModule level domain = Module (PureSentence domain)

-- |'PureDefinition' is the pure (fixed-@level@) version of 'Definition'
type PureDefinition level domain = Definition (PureSentence domain)

type ParsedSentenceSort =
    SentenceSort (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceSymbol =
    SentenceSymbol (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceAlias =
    SentenceAlias (ParsedPurePattern Object Domain.Builtin)

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
        SortVariable
        (ParsedPurePattern Object Domain.Builtin)

type ParsedModule = Module ParsedSentence

type ParsedDefinition = Definition ParsedSentence

castDefinitionDomainValues
    :: Functor domain
    => PureDefinition Object (Const Void)
    -> PureDefinition Object domain
castDefinitionDomainValues = (fmap . fmap) Pure.castVoidDomainValues
