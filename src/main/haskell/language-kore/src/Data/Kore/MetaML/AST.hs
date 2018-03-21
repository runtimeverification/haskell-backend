{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Module      : Data.Kore.MetaML.AST
Description : Data Structures for representing a Meta-only version of the
              Kore language AST
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module specializes the 'Data.Kore.AST.Common' datastructures for
representing definitions, modules, axioms, patterns that only use 'Meta'-level
constructs.

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Data.Kore.MetaML.AST where

import           Data.Fix

import           Data.Kore.AST.Common

{-|'MetaMLPattern' corresponds to "fixed point" representations
of the 'Pattern' class where the level is fixed to 'Meta'.

'var' is the type of variables.
-}
type MetaMLPattern var = Fix (Pattern Meta var)

-- |'MetaAttributes' is the 'Meta'-only version of 'Attributes'
type MetaAttributes = Attributes CommonMetaPattern

type MetaSentenceAxiom =
    SentenceAxiom (SortVariable Meta) CommonMetaPattern
type MetaSentenceAlias = SentenceAlias CommonMetaPattern Meta
type MetaSentenceSymbol = SentenceSymbol CommonMetaPattern Meta
type MetaSentenceImport = SentenceImport CommonMetaPattern

-- |'MetaAttributes' is the 'Meta'-only version of 'Sentence'.
-- Note that, as such, it does not contain sort definitions nor other 'Object'
-- sentences.
data MetaSentence
    = AliasMetaSentence !MetaSentenceAlias
    | SymbolMetaSentence !MetaSentenceSymbol
    | AxiomMetaSentence !MetaSentenceAxiom
    | ImportMetaSentence !MetaSentenceImport
    deriving (Eq, Show)

instance AsSentence MetaSentence (SentenceAlias CommonMetaPattern Meta) where
    asSentence = AliasMetaSentence

instance AsSentence MetaSentence (SentenceSymbol CommonMetaPattern Meta) where
    asSentence = SymbolMetaSentence

instance AsSentence MetaSentence (SentenceImport CommonMetaPattern) where
    asSentence = ImportMetaSentence

instance AsSentence MetaSentence
    (SentenceAxiom (SortVariable Meta) CommonMetaPattern)
  where
    asSentence = AxiomMetaSentence

-- |'MetaModule' is the 'Meta'-only version of 'Module'.
type MetaModule = Module MetaSentence CommonMetaPattern

-- |'MetaDefinition' is the 'Meta'-only version of 'Definition'.
type MetaDefinition = Definition MetaSentence CommonMetaPattern

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

type CommonMetaPattern = MetaMLPattern Variable
type PatternMetaType = Pattern Meta Variable CommonMetaPattern

type MetaPatternStub = PatternStub Meta Variable CommonMetaPattern

{-|'dummyMetaSort' is used in error messages when we want to convert an
'UnsortedPatternStub' to a pattern that can be displayed.
-}
dummyMetaSort :: Sort Meta
dummyMetaSort = SortVariableSort (SortVariable (Id "#dummy"))
