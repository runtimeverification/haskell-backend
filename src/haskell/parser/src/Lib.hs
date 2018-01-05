module Lib
    ( Definition,
      definitionParser
    ) where

import Text.Parsec.String (Parser)

newtype Id = Id String

data SymbolOrAlias = Symbol
    { symbolOrAliasCtr :: Id  -- Huh????
    , symbolOrAliasParams :: [Sort]
    }

data Symbol = Symbol
    { symbolCtr :: Id  -- Huh????
    , symbolParams :: [Sort]
    }

data Alias = Alias
    { aliasCtr :: Id  -- Huh????
    , aliasParams :: [Sort]
    }

newtype SortVariable = SortVariable Id

data Sort =
    SortVariableSort SortVariable
  | ActualSort
      { actualSortName :: Id
      , actualSortSorts :: [Sort]
      }

newtype ModuleName = ModuleName String

data Variable = Variable
  { variableName :: Id
  , variableSort :: Sort
  }

data Pattern =
    VariablePattern Variable
  | StringLiteralPattern StringLiteral
  | SymbolOrAliasPattern
      { symbolOrAlias :: SymbolOrAlias
      , patterns :: [Pattern]
      }
  | TopPattern Sort
  | BottomPattern Sort
  | AndPattern
      { andPatternSort :: Sort
      , andPatternFirst :: Pattern
      , andPatternSecond :: Pattern
      }
  | OrPattern
      { orPatternSort :: Sort
      , orPatternFirst :: Pattern
      , orPatternSecond :: Pattern
      }
  | NotPattern
      { notPatternSort :: Sort
      , notPatternPattern :: Pattern
      }
  | ImpliesPattern
      { impliesPatternSort :: Sort
      , impliesPatternFirst :: Pattern
      , impliesPatternSecond :: Pattern
      }
  | IffPattern
      { iffPatternSort :: Sort
      , iffPatternFirst :: Pattern
      , iffPatternSecond :: Pattern
      }
  | ExistsPattern
      { existsPatternSort :: Sort
      , existsPatternVariable :: Variable
      , existsPatternPattern :: Pattern
      }
  | ForallPattern
      { forallPatternSort :: Sort
      , forallPatternVariable :: Variable
      , forallPatternPattern :: Pattern
      }
  | NextPattern
      { nextPatternSort :: Sort
      , nextPatternPattern :: Pattern
      }
  | RewritesPattern
      { rewritesPatternFirstSort :: Sort
      , rewritesPatternSecondSort :: Sort
      , rewritesPatternFirst :: Pattern
      , rewritesPatternSecond :: Pattern
      }
  | EqualPattern
      { equalPatternFirstSort :: Sort
      , equalPatternSecondSort :: Sort
      , equalPatternFirst :: Pattern
      , equalPatternSecond :: Pattern
      }
  | MemPattern
      { memPatternFirstSort :: Sort
      , memPatternSecondSort :: Sort
      , memPatternVariable :: Variable
      , memPatternPattern :: Pattern
      }
  | SubsetPattern
      { subsetPatternFirstSort :: Sort
      , subsetPatternSecondSort :: Sort
      , subsetPatternFirst :: Pattern
      , subsetPatternSecond :: Pattern
      }
  | DomainValuePattern
      { domainValuePatternFirst :: StringLiteral
      , domainValuePatternSecond :: StringLiteral
      }

data Sentence =
    SortSentence
      { sortSentenceSortVariables :: [SortVariable]
      , sortSentenceSort :: Sort
      , sortSentenceAttributes :: [Attribute]
      }
  | SymbolSentence
      { symbolSentenceSymbol :: Symbol
      , symbolSentenceSorts :: [Sort]
      , symbolSentenceAttributes :: [Attribute]
      }
  | AliasSentence
      { aliasSentenceAlias :: Alias
      , aliasSentenceSorts :: [Sort]
      , aliasSentenceAttributes :: [Attribute]
      }
  | AxiomSentence
      { axiomSentenceSortVariables :: [SortVariable]
      , axiomSentenceAxiom :: Axiom
      }
  deriving (Show, Eq)

newtype Attribute = Attribute [Pattern]
  deriving (Show, Eq)

data Module = Module
  { moduleName :: String
  , moduleSentences :: [Sentence]
  , moduleAttributes :: [Attribute]
  }
  deriving (Show, Eq)

data Definition = Definition
  { definitionAttributes :: [Attribute]
  , definitionModules :: [Module]
  }
  deriving (Show, Eq)

definitionParser :: Parser Definition
definitionParser = do
    attributes <- attributesParser
    modules <- modulesParser
    return Definition
      { definitionAttributes = attributes
      , definitionModules = modules
      }

