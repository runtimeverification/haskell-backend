{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Data.Kore.AST.PureML where

import           Data.Fix
import           Data.Kore.AST.Common

{-|'PureMLPattern' corresponds to "fixed point" representations
of the 'Pattern' class where the level is fixed to a given @level@.

@var@ is the type of variables.
-}
type PureMLPattern level var = Fix (Pattern level var)

asPurePattern
    :: Pattern level var (PureMLPattern level var) -> PureMLPattern level var
asPurePattern = Fix

-- |'MetaAttributes' is the 'Meta'-only version of 'Attributes'
type PureAttributes level = Attributes (Pattern level) Variable

type PureSentenceAxiom level =
    SentenceAxiom (SortVariable level) (Pattern level) Variable
type PureSentenceAlias level =
    SentenceAlias level (Pattern level) Variable
type PureSentenceSymbol level =
    SentenceSymbol level (Pattern level) Variable
type PureSentenceImport level =
    SentenceImport (Pattern level) Variable

type PureSentence level =
    Sentence level (SortVariable level) (Pattern level) Variable

instance AsSentence (PureSentence level) (PureSentenceAlias level) where
    asSentence = SentenceAliasSentence

instance AsSentence (PureSentence level) (PureSentenceSymbol level) where
    asSentence = SentenceSymbolSentence

-- |'PureModule' is the pure version of 'Module', with a fixed @level@.
type PureModule level =
    Module (Sentence level) (SortVariable level) (Pattern level) Variable

-- |'PureDefinition' is the pure version of 'Definition', with a fixed @level@.
type PureDefinition level =
    Definition
        (Sentence level) (SortVariable level) (Pattern level) Variable

groundHead :: String -> SymbolOrAlias level
groundHead ctor = SymbolOrAlias
    { symbolOrAliasConstructor = Id ctor
    , symbolOrAliasParams = []
    }

groundSymbol :: String -> Symbol level
groundSymbol ctor = Symbol
    { symbolConstructor = Id ctor
    , symbolParams = []
    }

apply :: SymbolOrAlias level -> [child] -> Pattern level variable child
apply patternHead patterns = ApplicationPattern Application
    { applicationSymbolOrAlias = patternHead
    , applicationChildren = patterns
    }

constant
    :: SymbolOrAlias level -> Pattern level variable child
constant patternHead = apply patternHead []

type CommonPurePattern level = PureMLPattern level Variable
type PatternPureType level = Pattern level Variable (CommonPurePattern level)

type PurePatternStub level =
    PatternStub level Variable (CommonPurePattern level)
