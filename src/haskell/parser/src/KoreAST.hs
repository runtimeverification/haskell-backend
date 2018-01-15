module KoreAST where

newtype Id = Id String
  deriving (Show, Eq)

newtype MetaId = MetaId String
  deriving (Show, Eq)

newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq)

data ObjectSymbolOrAlias = ObjectSymbolOrAlias
    { objectSymbolOrAliasConstructor :: !Id
    , objectSymbolOrAliasParams      :: ![ObjectSort]
    }
    deriving (Show, Eq)

data ObjectSymbol = ObjectSymbol
    { objectSymbolConstructor :: !Id
    , objectSymbolParams      :: ![ObjectSort]
    }
    deriving (Show, Eq)

data ObjectAlias = ObjectAlias
    { objectAliasConstructor :: !Id
    , objectAliasParams      :: ![ObjectSort]
    }
    deriving (Show, Eq)

data MetaSymbolOrAlias = MetaSymbolOrAlias
    { metaSymbolOrAliasConstructor :: !MetaId
    , metaSymbolOrAliasParams      :: ![MetaSort]
    }
    deriving (Show, Eq)

data MetaSymbol = MetaSymbol
    { metaSymbolConstructor :: !MetaId
    , metaSymbolParams      :: ![MetaSort]
    }
    deriving (Show, Eq)

data MetaAlias = MetaAlias
    { metaAliasConstructor :: !MetaId
    , metaAliasParams      :: ![MetaSort]
    }
    deriving (Show, Eq)

newtype ObjectSortVariable = ObjectSortVariable { getObjectSortVariable :: Id }
    deriving (Show, Eq)

data ObjectSort
    = ObjectSortVariableSort !ObjectSortVariable
    | ActualSort
        { actualSortName  :: !Id
        , actualSortSorts :: ![ObjectSort]
        }
    deriving (Show, Eq)

newtype MetaSortVariable = MetaSortVariable { getMetaSortVariable :: MetaId }
    deriving (Show, Eq)

data SortVariable
    = ObjectSortVariableSortVariable ObjectSortVariable
    | MetaSortVariableSortVariable MetaSortVariable
    deriving (Show, Eq)

data MetaSort
    = MetaSortVariableMetaSort !MetaSortVariable
    | CharMetaSort
    | CharListMetaSort
    | PatternMetaSort
    | PatternListMetaSort
    | SortMetaSort
    | SortListMetaSort
    | StringMetaSort
    | SymbolMetaSort
    | SymbolListMetaSort
    | VariableMetaSort
    | VariableListMetaSort
    deriving (Show, Eq)

newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq)

data Variable = Variable
    { variableName :: !Id
    , variableSort :: !ObjectSort
    }
    deriving (Show, Eq)

data Pattern
    = AndPattern
        { andPatternSort   :: !ObjectSort
        , andPatternFirst  :: !Pattern
        , andPatternSecond :: !Pattern
        }
    | ApplicationPattern
        { applicationPatternSymbolOrAlias :: !ObjectSymbolOrAlias
        , applicationPatternPatterns      :: ![Pattern]
        }
    | BottomPattern !ObjectSort
    | CeilPattern
        { ceilPatternFirstSort  :: !ObjectSort
        , ceilPatternSecondSort :: !ObjectSort
        , ceilPatternPattern    :: !Pattern
        }
    | EqualsPattern
        { equalsPatternFirstSort  :: !ObjectSort
        , equalsPatternSecondSort :: !ObjectSort
        , equalsPatternFirst      :: !Pattern
        , equalsPatternSecond     :: !Pattern
        }
    | ExistsPattern
        { existsPatternSort     :: !ObjectSort
        , existsPatternVariable :: !Variable
        , existsPatternPattern  :: !Pattern
        }
    | FloorPattern
        { floorPatternFirstSort  :: !ObjectSort
        , floorPatternSecondSort :: !ObjectSort
        , floorPatternPattern    :: !Pattern
        }
    | ForallPattern
        { forallPatternSort     :: !ObjectSort
        , forallPatternVariable :: !Variable
        , forallPatternPattern  :: !Pattern
        }
    | IffPattern
        { iffPatternSort   :: !ObjectSort
        , iffPatternFirst  :: !Pattern
        , iffPatternSecond :: !Pattern
        }
    | ImpliesPattern
        { impliesPatternSort   :: !ObjectSort
        , impliesPatternFirst  :: !Pattern
        , impliesPatternSecond :: !Pattern
        }
    | MemPattern
        { memPatternFirstSort  :: !ObjectSort
        , memPatternSecondSort :: !ObjectSort
        , memPatternVariable   :: !Variable
        , memPatternPattern    :: !Pattern
        }
    | NotPattern
        { notPatternSort    :: !ObjectSort
        , notPatternPattern :: !Pattern
        }
    | OrPattern
        { orPatternSort   :: !ObjectSort
        , orPatternFirst  :: !Pattern
        , orPatternSecond :: !Pattern
        }
    | StringLiteralPattern !StringLiteral
    | TopPattern !ObjectSort
    | VariablePattern !Variable
    deriving (Show, Eq)

data Sentence
    = AliasSentence
        { aliasSentenceAlias      :: !ObjectAlias
        , aliasSentenceSorts      :: ![ObjectSort]
        , aliasSentenceReturnSort :: !ObjectSort
        , aliasSentenceAttributes :: !Attributes
        }
    | AxiomSentence
        { axiomSentenceParameters :: ![SortVariable]
        , axiomSentencePattern    :: !Pattern
        , axiomSentenceAtrributes :: !Attributes
        }
    | SortSentence
        { sortSentenceParameters :: ![SortVariable]
        , sortSentenceSort       :: !ObjectSort
        , sortSentenceAttributes :: !Attributes
        }
    | SymbolSentence
        { symbolSentenceSymbol     :: !ObjectSymbol
        , symbolSentenceSorts      :: ![ObjectSort]
        , symbolSentenceReturnSort :: !ObjectSort
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
    , definitionModules    :: !Module
    }
    deriving (Show, Eq)
