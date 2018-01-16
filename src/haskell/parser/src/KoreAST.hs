module KoreAST where

data MetaType
    = ObjectType
    | MetaType
    deriving (Eq, Show)

class Show a => IsMeta a where
    metaType :: a -> MetaType

data Meta = Meta
    deriving (Show, Eq)

instance IsMeta Meta where
    metaType _ = MetaType

data Object = Object
    deriving (Show, Eq)

instance IsMeta Object where
    metaType _ = ObjectType

data Id a = Id { idType :: !a, getId :: !String }
    deriving (Show, Eq)

newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq)

data SymbolOrAlias a = SymbolOrAlias
    { symbolOrAliasType        :: !a
    , symbolOrAliasConstructor :: !(Id a)
    , symbolOrAliasParams      :: ![Sort a]
    }
    deriving (Show, Eq)

data Symbol a = Symbol
    { symbolType        :: !a
    , symbolConstructor :: !(Id a)
    , symbolParams      :: ![Sort a]
    }
    deriving (Show, Eq)

data Alias a = Alias
    { aliasType        :: !a
    , aliasConstructor :: !(Id a)
    , aliasParams      :: ![Sort a]
    }
    deriving (Show, Eq)

data SortVariable a = SortVariable
    { sortVariableType :: !a
    , getSortVariable  :: !(Id a)
    }
    deriving (Show, Eq)

data Sort a
    = SortVariableSort
        { sortVariableSortType :: !a
        , getSortVariableSort  :: !(SortVariable a)
        }
    | ActualSort
        { actualSortType  :: !a
        , actualSortName  :: !(Id a)
        , actualSortSorts :: ![Sort a]
        }
    deriving (Show, Eq)

data MetaSortType
    = CharSort
    | CharListSort
    | PatternSort
    | PatternListSort
    | SortSort
    | SortListSort
    | StringSort
    | SymbolSort
    | SymbolListSort
    | VariableSort
    | VariableListSort

instance Show MetaSortType where
    show CharSort         = "#Char"
    show CharListSort     = "#CharList"
    show PatternSort      = "#Pattern"
    show PatternListSort  = "#PatternList"
    show SortSort         = "#Sort"
    show SortListSort     = "#SortList"
    show StringSort       = "#String"
    show SymbolSort       = "#Symbol"
    show SymbolListSort   = "#SymbolList"
    show VariableSort     = "#Variable"
    show VariableListSort = "#VariableList"

data UnifiedSortVariable
    = ObjectSortVariable !(SortVariable Object)
    | MetaSortVariable !(SortVariable Meta)
    deriving (Show, Eq)

newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq)

data Variable a = Variable
    { variableType :: a
    , variableName :: !(Id a)
    , variableSort :: !(Sort a)
    }
    deriving (Show, Eq)

data UnifiedVariable
    = MetaVariable !(Variable Meta)
    | ObjectVariable !(Variable Object)
    deriving (Eq, Show)

data UnifiedPattern
    = MetaPattern !(Pattern Meta)
    | ObjectPattern !(Pattern Object)
    deriving (Eq, Show)

data Pattern a
    = AndPattern
        { andPatternSort   :: !(Sort a)
        , andPatternFirst  :: !UnifiedPattern
        , andPatternSecond :: !UnifiedPattern
        }
    | ApplicationPattern
        { applicationPatternSymbolOrAlias :: !(SymbolOrAlias a)
        , applicationPatternPatterns      :: ![UnifiedPattern]
        }
    | BottomPattern !(Sort a)
    | CeilPattern
        { ceilPatternFirstSort  :: !(Sort a)
        , ceilPatternSecondSort :: !(Sort a)
        , ceilPatternPattern    :: !UnifiedPattern
        }
    | EqualsPattern
        { equalsPatternFirstSort  :: !(Sort a)
        , equalsPatternSecondSort :: !(Sort a)
        , equalsPatternFirst      :: !UnifiedPattern
        , equalsPatternSecond     :: !UnifiedPattern
        }
    | ExistsPattern
        { existsPatternSort     :: !(Sort a)
        , existsPatternVariable :: !UnifiedVariable
        , existsPatternPattern  :: !UnifiedPattern
        }
    | FloorPattern
        { floorPatternFirstSort  :: !(Sort a)
        , floorPatternSecondSort :: !(Sort a)
        , floorPatternPattern    :: !UnifiedPattern
        }
    | ForallPattern
        { forallPatternSort     :: !(Sort a)
        , forallPatternVariable :: !UnifiedVariable
        , forallPatternPattern  :: !UnifiedPattern
        }
    | IffPattern
        { iffPatternSort   :: !(Sort a)
        , iffPatternFirst  :: !UnifiedPattern
        , iffPatternSecond :: !UnifiedPattern
        }
    | ImpliesPattern
        { impliesPatternSort   :: !(Sort a)
        , impliesPatternFirst  :: !UnifiedPattern
        , impliesPatternSecond :: !UnifiedPattern
        }
    | MemPattern
        { memPatternFirstSort  :: !(Sort a)
        , memPatternSecondSort :: !(Sort a)
        , memPatternVariable   :: !UnifiedVariable
        , memPatternPattern    :: !UnifiedPattern
        }
    | NotPattern
        { notPatternSort    :: !(Sort a)
        , notPatternPattern :: !UnifiedPattern
        }
    | OrPattern
        { orPatternSort   :: !(Sort a)
        , orPatternFirst  :: !UnifiedPattern
        , orPatternSecond :: !UnifiedPattern
        }
    | StringLiteralPattern !StringLiteral
    | TopPattern !(Sort a)
    | VariablePattern !(Variable a)
    deriving (Eq, Show)

data SymbolOrAliasSentence a
    = AliasSentence
        { aliasSentenceAlias      :: !(Alias a)
        , aliasSentenceSorts      :: ![Sort a]
        , aliasSentenceReturnSort :: !(Sort a)
        , aliasSentenceAttributes :: !Attributes
        }
    | SymbolSentence
        { symbolSentenceSymbol     :: !(Symbol a)
        , symbolSentenceSorts      :: ![Sort a]
        , symbolSentenceReturnSort :: !(Sort a)
        , symbolSentenceAttributes :: !Attributes
        }
    deriving (Eq, Show)

data Sentence
    = MetaSymbolOrAliasSentence !(SymbolOrAliasSentence Meta)
    | ObjectSymbolOrAliasSentence !(SymbolOrAliasSentence Object)
    | AxiomSentence
        { axiomSentenceParameters :: ![UnifiedSortVariable]
        , axiomSentencePattern    :: !UnifiedPattern
        , axiomSentenceAtrributes :: !Attributes
        }
    | SortSentence
        { sortSentenceParameters :: ![UnifiedSortVariable]
        , sortSentenceSort       :: !(Sort Object)
        , sortSentenceAttributes :: !Attributes
        }
    deriving (Eq, Show)

newtype Attributes = Attributes { getAttributes :: [UnifiedPattern] }
    deriving (Eq, Show)

data Module = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![Sentence]
    , moduleAttributes :: !Attributes
    }
    deriving (Eq, Show)

data Definition = Definition
    { definitionAttributes :: !Attributes
    , definitionModules    :: !Module
    }
    deriving (Eq, Show)
