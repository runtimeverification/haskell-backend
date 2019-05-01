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

import           Kore.AST.Pure as Pure
import           Kore.Attribute.Attributes
import qualified Kore.Domain.Builtin as Domain
import           Kore.Syntax.Definition

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

instance
    AsSentence
        (Sentence
            (PurePattern Object domain variable annotation)
        )
        (SentenceAlias (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceAliasSentence

instance
    AsSentence
        (Sentence
            (PurePattern Object domain variable annotation)
        )
        (SentenceSymbol (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceSymbolSentence

instance
    AsSentence
        (Sentence
            (PurePattern Object domain variable annotation)
        )
        (SentenceImport (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceImportSentence

instance
    AsSentence
        (Sentence
            (PurePattern Object domain variable annotation)
        )
        (SentenceAxiom (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceAxiomSentence

instance
    AsSentence
        (Sentence
            (PurePattern Object domain variable annotation)
        )
        (SentenceSort (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceSortSentence


instance
    AsSentence
        (Sentence
            (PurePattern Object domain variable annotation)
        )
        (SentenceHook (PurePattern Object domain variable annotation))
  where
    asSentence = SentenceHookSentence

type ParsedSentenceSort =
    SentenceSort (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceSymbol =
    SentenceSymbol (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceAlias =
    SentenceAlias (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceImport =
    SentenceImport (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceAxiom =
    SentenceAxiom (ParsedPurePattern Object Domain.Builtin)

type ParsedSentenceHook =
    SentenceHook (ParsedPurePattern Object Domain.Builtin)

type ParsedSentence = Sentence (ParsedPurePattern Object Domain.Builtin)

type ParsedModule = Module ParsedSentence

type ParsedDefinition = Definition ParsedSentence
