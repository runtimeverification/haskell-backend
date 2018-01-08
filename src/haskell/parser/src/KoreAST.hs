module KoreAST where

newtype Id = Id String
  deriving (Show, Eq)

newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq)

data SymbolOrAlias = SymbolOrAlias
    { symbolOrAliasConstructor :: !Id
    , symbolOrAliasParams :: ![Sort]
    }
    deriving (Show, Eq)

data Symbol = Symbol
    { symbolConstructor :: !Id
    , symbolParams :: ![Sort]
    }
    deriving (Show, Eq)

data Alias = Alias
    { aliasConstructor :: !Id
    , aliasParams :: ![Sort]
    }
    deriving (Show, Eq)

newtype SortVariable = SortVariable { getSortVariable :: Id }
    deriving (Show, Eq)

data Sort
    = SortVariableSort !SortVariable
    | ActualSort
        { actualSortName :: !Id
        , actualSortSorts :: ![Sort]
        }
    deriving (Show, Eq)

newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq)

data Variable = Variable
    { variableName :: !Id
    , variableSort :: !Sort
    }
    deriving (Show, Eq)

data Pattern
    = VariablePattern !Variable
    | StringLiteralPattern !StringLiteral
    | SymbolOrAliasPattern
        { symbolOrAlias :: !SymbolOrAlias
        , patterns :: ![Pattern]
        }
    | TopPattern !Sort
    | BottomPattern !Sort
    | AndPattern
        { andPatternSort :: !Sort
        , andPatternFirst :: !Pattern
        , andPatternSecond :: !Pattern
        }
    | OrPattern
        { orPatternSort :: !Sort
        , orPatternFirst :: !Pattern
        , orPatternSecond :: !Pattern
        }
    | NotPattern
        { notPatternSort :: !Sort
        , notPatternPattern :: !Pattern
        }
    | ImpliesPattern
        { impliesPatternSort :: !Sort
        , impliesPatternFirst :: !Pattern
        , impliesPatternSecond :: !Pattern
        }
    | IffPattern
        { iffPatternSort :: !Sort
        , iffPatternFirst :: !Pattern
        , iffPatternSecond :: !Pattern
        }
    | ExistsPattern
        { existsPatternSort :: !Sort
        , existsPatternVariable :: !Variable
        , existsPatternPattern :: !Pattern
        }
    | ForallPattern
        { forallPatternSort :: !Sort
        , forallPatternVariable :: !Variable
        , forallPatternPattern :: !Pattern
        }
    | NextPattern
        { nextPatternSort :: !Sort
        , nextPatternPattern :: !Pattern
        }
    | RewritesPattern
        { rewritesPatternFirstSort :: !Sort
        , rewritesPatternSecondSort :: !Sort
        , rewritesPatternFirst :: !Pattern
        , rewritesPatternSecond :: !Pattern
        }
    | EqualPattern
        { equalPatternFirstSort :: !Sort
        , equalPatternSecondSort :: !Sort
        , equalPatternFirst :: !Pattern
        , equalPatternSecond :: !Pattern
        }
    | MemPattern
        { memPatternFirstSort :: !Sort
        , memPatternSecondSort :: !Sort
        , memPatternVariable :: !Variable
        , memPatternPattern :: !Pattern
        }
    | SubsetPattern
        { subsetPatternFirstSort :: !Sort
        , subsetPatternSecondSort :: !Sort
        , subsetPatternFirst :: !Pattern
        , subsetPatternSecond :: !Pattern
        }
    | DomainValuePattern
        { domainValuePatternFirst :: !StringLiteral
        , domainValuePatternSecond :: !StringLiteral
        }
    deriving (Show, Eq)

data Axiom = Axiom
    { axiomSortVariables :: ![SortVariable]
    , axiomPattern :: !Pattern
    , axiomAttributes :: !Attributes
    }
    deriving (Show, Eq)

data Sentence
    = SortSentence
        { sortSentenceSortVariables :: ![SortVariable]
        , sortSentenceSort :: !Sort
        , sortSentenceAttributes :: !Attributes
        }
    | SymbolSentence
        { symbolSentenceSymbol :: !Symbol
        , symbolSentenceSorts :: ![Sort]
        , symbolSentenceAttributes :: !Attributes
        }
    | AliasSentence
        { aliasSentenceAlias :: !Alias
        , aliasSentenceSorts :: ![Sort]
        , aliasSentenceAttributes :: !Attributes
        }
    | AxiomSentence
        { axiomSentenceSortVariables :: ![SortVariable]
        , axiomSentenceAxiom :: !Axiom
        }
    deriving (Show, Eq)

newtype Attributes = Attributes { getAttributes :: [Pattern] }
    deriving (Show, Eq)

data Module = Module
    { moduleName :: !String
    , moduleSentences :: ![Sentence]
    , moduleAttributes :: !Attributes
    }
    deriving (Show, Eq)

data Definition = Definition
    { definitionAttributes :: !Attributes
    , definitionModules :: ![Module]
    }
    deriving (Show, Eq)

--definitionParser :: Parser Definition
--definitionParser = do
--    attributes <- attributesParser
--    modules <- modulesParser
--    return Definition
--      { definitionAttributes = attributes
--      , definitionModules = modules
--      }

