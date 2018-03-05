module Data.Kore.MetaML.AST where

import           Data.Fix

import           Data.Kore.AST

type MetaMLPattern var = Fix (Pattern Meta var)

data MetaSentenceAxiom = MetaSentenceAxiom
    { metaSentenceAxiomParameters :: ![SortVariable Meta]
    , metaSentenceAxiomPattern    :: !(MetaMLPattern Variable)
    , metaSentenceAxiomAttributes :: !Attributes
    }
    deriving (Eq, Show)

groundHead :: String -> SymbolOrAlias a
groundHead name = SymbolOrAlias
    { symbolOrAliasConstructor = Id name
    , symbolOrAliasParams = []
    }

apply :: SymbolOrAlias a -> [p] -> Pattern a v p
apply patternHead patterns = ApplicationPattern Application
    { applicationSymbolOrAlias = patternHead
    , applicationChildren = patterns
    }

constant :: SymbolOrAlias a -> Pattern a v p
constant patternHead = apply patternHead []

nilSortListHead :: SymbolOrAlias Meta
nilSortListHead = groundHead "#nilSortList"

consSortListHead :: SymbolOrAlias Meta
consSortListHead = groundHead "#consSortList"

nilSortListMetaPattern :: MetaMLPattern v
nilSortListMetaPattern = Fix $ constant nilSortListHead

nilPatternListHead :: SymbolOrAlias Meta
nilPatternListHead = groundHead "#nilPatternList"

consPatternListHead :: SymbolOrAlias Meta
consPatternListHead = groundHead "#consPatternList"

nilPatternListMetaPattern :: MetaMLPattern v
nilPatternListMetaPattern = Fix $ constant nilPatternListHead

variableHead :: SymbolOrAlias Meta
variableHead = groundHead "#variable"

variableAsPatternHead :: SymbolOrAlias Meta
variableAsPatternHead = groundHead "#variableAsPattern"

andHead :: SymbolOrAlias Meta
andHead = groundHead "#\\and"

bottomHead :: SymbolOrAlias Meta
bottomHead = groundHead "#\\bottom"

ceilHead :: SymbolOrAlias Meta
ceilHead = groundHead "#\\ceil"

equalsHead :: SymbolOrAlias Meta
equalsHead = groundHead "#\\equals"

existsHead :: SymbolOrAlias Meta
existsHead = groundHead "#\\equals"

floorHead :: SymbolOrAlias Meta
floorHead = groundHead "#\\floor"

forallHead :: SymbolOrAlias Meta
forallHead = groundHead "#\\forall"

iffHead :: SymbolOrAlias Meta
iffHead = groundHead "#\\iff"

impliesHead :: SymbolOrAlias Meta
impliesHead = groundHead "#\\implies"

inHead :: SymbolOrAlias Meta
inHead = groundHead "#\\in"

nextHead :: SymbolOrAlias Meta
nextHead = groundHead "#\\next"

notHead :: SymbolOrAlias Meta
notHead = groundHead "#\\not"

orHead :: SymbolOrAlias Meta
orHead = groundHead "#\\or"

rewritesHead :: SymbolOrAlias Meta
rewritesHead = groundHead "#\\rewrites"

topHead :: SymbolOrAlias Meta
topHead = groundHead "#\\top"
