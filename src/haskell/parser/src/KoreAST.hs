module KoreAST where

newtype Id = Id String
  deriving (Show, Eq)

newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq)

data SymbolOrAlias = SymbolOrAlias
    { symbolOrAliasConstructor :: !Id
    , symbolOrAliasParams      :: ![Sort]
    }
    deriving (Show, Eq)

data Symbol = Symbol
    { symbolConstructor :: !Id
    , symbolParams      :: ![Sort]
    }
    deriving (Show, Eq)

data Alias = Alias
    { aliasConstructor :: !Id
    , aliasParams      :: ![Sort]
    }
    deriving (Show, Eq)

newtype SortVariable = SortVariable { getSortVariable :: Id }
    deriving (Show, Eq)

data Sort
    = SortVariableSort !SortVariable
    | ActualSort
        { actualSortName  :: !Id
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
    = AndPattern
        { andPatternSort   :: !Sort
        , andPatternFirst  :: !Pattern
        , andPatternSecond :: !Pattern
        }
    | BottomPattern !Sort
    | CeilPattern
        { ceilPatternFirstSort  :: !Sort
        , ceilPatternSecondSort :: !Sort
        , ceilPatternPattern    :: !Pattern
        }
     | DomainValuePattern
        { domainValuePatternFirst  :: !StringLiteral
        , domainValuePatternSecond :: !StringLiteral
        }
    | EqualsPattern
        { equalsPatternFirstSort  :: !Sort
        , equalsPatternSecondSort :: !Sort
        , equalsPatternFirst      :: !Pattern
        , equalsPatternSecond     :: !Pattern
        }
    | ExistsPattern
        { existsPatternSort     :: !Sort
        , existsPatternVariable :: !Variable
        , existsPatternPattern  :: !Pattern
        }
    | FloorPattern
        { floorPatternFirstSort  :: !Sort
        , floorPatternSecondSort :: !Sort
        , floorPatternPattern    :: !Pattern
        }
    | ForallPattern
        { forallPatternSort     :: !Sort
        , forallPatternVariable :: !Variable
        , forallPatternPattern  :: !Pattern
        }
    | IffPattern
        { iffPatternSort   :: !Sort
        , iffPatternFirst  :: !Pattern
        , iffPatternSecond :: !Pattern
        }
    | ImpliesPattern
        { impliesPatternSort   :: !Sort
        , impliesPatternFirst  :: !Pattern
        , impliesPatternSecond :: !Pattern
        }
    | MemPattern
        { memPatternFirstSort  :: !Sort
        , memPatternSecondSort :: !Sort
        , memPatternVariable   :: !Variable
        , memPatternPattern    :: !Pattern
        }
    | NextPattern
        { nextPatternSort    :: !Sort
        , nextPatternPattern :: !Pattern
        }
    | NotPattern
        { notPatternSort    :: !Sort
        , notPatternPattern :: !Pattern
        }
    | OrPattern
        { orPatternSort   :: !Sort
        , orPatternFirst  :: !Pattern
        , orPatternSecond :: !Pattern
        }
    | RewritesPattern
        { rewritesPatternFirstSort  :: !Sort
        , rewritesPatternSecondSort :: !Sort
        , rewritesPatternFirst      :: !Pattern
        , rewritesPatternSecond     :: !Pattern
        }
    | StringLiteralPattern !StringLiteral
    | SubsetPattern
        { subsetPatternFirstSort  :: !Sort
        , subsetPatternSecondSort :: !Sort
        , subsetPatternFirst      :: !Pattern
        , subsetPatternSecond     :: !Pattern
        }
    | ApplicationPattern
        { applicationPatternSymbolOrAlias :: !SymbolOrAlias
        , applicationPatternPatterns      :: ![Pattern]
        }
    | TopPattern !Sort
    | VariablePattern !Variable
    deriving (Show, Eq)

data Sentence
    = AliasSentence
        { aliasSentenceAlias      :: !Alias
        , aliasSentenceSorts      :: ![Sort]
        , aliasSentenceReturnSort :: !Sort
        , aliasSentenceAttributes :: !Attributes
        }
    | AxiomSentence
        { axiomSentenceParameters :: ![SortVariable]
        , axiomSentencePattern    :: !Pattern
        , axiomSentenceAtrributes :: Attributes
        }
    | ImportSentence
        { importModuleName :: !ModuleName
        , importAttributes :: !Attributes
        }
    | SortSentence
        { sortSentenceParameters :: ![SortVariable]
        , sortSentenceSort       :: !Sort
        , sortSentenceAttributes :: !Attributes
        }
    | SymbolSentence
        { symbolSentenceSymbol     :: !Symbol
        , symbolSentenceSorts      :: ![Sort]
        , symbolSentenceReturnSort :: !Sort
        , symbolSentenceAttributes :: !Attributes
        }
   deriving (Show, Eq)

newtype Attributes = Attributes { getAttributes :: [Pattern] }
    deriving (Show, Eq)

data Module = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![Sentence]
    , moduleAttributes :: !Attributes
    }
    deriving (Show, Eq)

data Definition = Definition
    { definitionAttributes :: !Attributes
    , definitionModules    :: ![Module]
    }
    deriving (Show, Eq)
