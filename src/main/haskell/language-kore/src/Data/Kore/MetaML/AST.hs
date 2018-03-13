module Data.Kore.MetaML.AST where

import           Data.Fix

import           Data.Kore.AST.Common

type MetaMLPattern var = Fix (Pattern Meta var)

newtype MetaAttributes = MetaAttributes
    { getMetaAttributes :: [MetaMLPattern Variable] }
  deriving (Eq, Show)

type MetaSentenceAxiom =
    SentenceAxiom (SortVariable Meta) (MetaMLPattern Variable) MetaAttributes
type MetaSentenceAlias = SentenceAlias MetaAttributes Meta
type MetaSentenceSymbol = SentenceSymbol MetaAttributes Meta
type MetaSentenceImport = SentenceImport MetaAttributes

data MetaSentence
    = AliasMetaSentence !MetaSentenceAlias
    | SymbolMetaSentence !MetaSentenceSymbol
    | AxiomMetaSentence !MetaSentenceAxiom
    | ImportMetaSentence !MetaSentenceImport
    deriving (Eq, Show)

data MetaModule = MetaModule
    { metaModuleName       :: !ModuleName
    , metaModuleSentences  :: ![MetaSentence]
    , metaModuleAttributes :: !MetaAttributes
    }
    deriving (Eq, Show)

groundHead :: Id a -> SymbolOrAlias a
groundHead ctor = SymbolOrAlias
    { symbolOrAliasConstructor = ctor
    , symbolOrAliasParams = []
    }

groundSymbol :: Id a -> Symbol a
groundSymbol ctor = Symbol
    { symbolConstructor = ctor
    , symbolParams = []
    }

apply :: SymbolOrAlias a -> [p] -> Pattern a v p
apply patternHead patterns = ApplicationPattern Application
    { applicationSymbolOrAlias = patternHead
    , applicationChildren = patterns
    }

constant :: SymbolOrAlias a -> Pattern a v p
constant patternHead = apply patternHead []

nilSortListHead :: SymbolOrAlias Meta
nilSortListHead = groundHead (Id "#nilSortList")

consSortListHead :: SymbolOrAlias Meta
consSortListHead = groundHead (Id "#consSortList")

nilSortListMetaPattern :: MetaMLPattern v
nilSortListMetaPattern = Fix $ constant nilSortListHead

nilPatternListHead :: SymbolOrAlias Meta
nilPatternListHead = groundHead (Id "#nilPatternList")

consPatternListHead :: SymbolOrAlias Meta
consPatternListHead = groundHead (Id "#consPatternList")

nilPatternListMetaPattern :: MetaMLPattern v
nilPatternListMetaPattern = Fix $ constant nilPatternListHead

variableHead :: SymbolOrAlias Meta
variableHead = groundHead (Id "#variable")

variableAsPatternHead :: SymbolOrAlias Meta
variableAsPatternHead = groundHead (Id "#variableAsPattern")

metaMLPatternHead :: MLPatternType -> SymbolOrAlias Meta
metaMLPatternHead pt = groundHead (Id ('#' : '\\' : patternString pt))

sortDeclaredHead :: Sort Meta -> SymbolOrAlias Meta
sortDeclaredHead param = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#sortDeclared"
    , symbolOrAliasParams = [param]
    }

sortsDeclaredHead :: Sort Meta -> SymbolOrAlias Meta
sortsDeclaredHead param = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#sortsDeclared"
    , symbolOrAliasParams = [param]
    }

symbolDeclaredHead :: Sort Meta -> SymbolOrAlias Meta
symbolDeclaredHead param = SymbolOrAlias
    { symbolOrAliasConstructor = Id "#symbolDeclared"
    , symbolOrAliasParams = [param]
    }

sortHead :: SymbolOrAlias Meta
sortHead = groundHead (Id "#sort")

symbolHead :: SymbolOrAlias Meta
symbolHead = groundHead (Id "#symbol")

applicationHead :: SymbolOrAlias Meta
applicationHead = groundHead (Id "#application")
