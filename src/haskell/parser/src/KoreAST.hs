{-# LANGUAGE ExistentialQuantification #-}
module KoreAST where

data MetaType
    = ObjectType
    | MetaType
    deriving (Eq, Show)

class IsMeta a where
    object :: a
    metaType :: a -> MetaType
    idConstructor :: a -> (String -> Id a)

data Meta = Meta
    deriving (Show)

instance IsMeta Meta where
    object = Meta
    metaType _ = MetaType
    idConstructor _ = Id

data Object = Object
    deriving (Show)

instance IsMeta Object where
    object = Object
    metaType _ = ObjectType
    idConstructor _ = Id

newtype Id a = Id { getId :: String }
    deriving (Show, Eq)

newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq)

data SymbolOrAlias a = SymbolOrAlias
    { symbolOrAliasConstructor :: !(Id a)
    , symbolOrAliasParams      :: ![Sort a]
    }
    deriving (Show, Eq)

data Symbol a = Symbol
    { symbolConstructor :: !(Id a)
    , symbolParams      :: ![Sort a]
    }
    deriving (Show, Eq)

data Alias a = Alias
    { objectAliasConstructor :: !(Id a)
    , objectAliasParams      :: ![Sort a]
    }
    deriving (Show, Eq)

newtype SortVariable a = SortVariable { getSortVariable :: Id a}
    deriving (Show, Eq)

data Sort a
    = SortVariableSort !(SortVariable a)
    | ActualSort
        { actualSortName  :: !(Id a)
        , actualSortSorts :: ![Sort a]
        }
    deriving (Show, Eq)

data UnifiedSortVariable
    = ObjectSortVariable !(SortVariable Object)
    | MetaSortVariable !(SortVariable Meta)
    deriving (Show, Eq)

newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq)

data Variable a = Variable
    { variableName :: !(Id a)
    , variableSort :: !(Sort a)
    }
    deriving (Show, Eq)

data Pattern
    = forall a . AndPattern
        { andPatternSort   :: !(Sort a)
        , andPatternFirst  :: !Pattern
        , andPatternSecond :: !Pattern
        }
    | forall a . ApplicationPattern
        { applicationPatternSymbolOrAlias :: !(SymbolOrAlias a)
        , applicationPatternPatterns      :: ![Pattern]
        }
    | forall a . BottomPattern !(Sort a)
    | forall a . CeilPattern
        { ceilPatternFirstSort  :: !(Sort a)
        , ceilPatternSecondSort :: !(Sort a)
        , ceilPatternPattern    :: !Pattern
        }
    | forall a . EqualsPattern
        { equalsPatternFirstSort  :: !(Sort a)
        , equalsPatternSecondSort :: !(Sort a)
        , equalsPatternFirst      :: !Pattern
        , equalsPatternSecond     :: !Pattern
        }
    | forall a . ExistsPattern
        { existsPatternSort     :: !(Sort a)
        , existsPatternVariable :: !(Variable a)
        , existsPatternPattern  :: !Pattern
        }
    | forall a . FloorPattern
        { floorPatternFirstSort  :: !(Sort a)
        , floorPatternSecondSort :: !(Sort a)
        , floorPatternPattern    :: !Pattern
        }
    | forall a . ForallPattern
        { forallPatternSort     :: !(Sort a)
        , forallPatternVariable :: !(Variable a)
        , forallPatternPattern  :: !Pattern
        }
    | forall a . IffPattern
        { iffPatternSort   :: !(Sort a)
        , iffPatternFirst  :: !Pattern
        , iffPatternSecond :: !Pattern
        }
    | forall a . ImpliesPattern
        { impliesPatternSort   :: !(Sort a)
        , impliesPatternFirst  :: !Pattern
        , impliesPatternSecond :: !Pattern
        }
    | forall a . MemPattern
        { memPatternFirstSort  :: !(Sort a)
        , memPatternSecondSort :: !(Sort a)
        , memPatternVariable   :: !Pattern
        , memPatternPattern    :: !Pattern
        }
    | forall a . NotPattern
        { notPatternSort    :: !(Sort a)
        , notPatternPattern :: !Pattern
        }
    | forall a . OrPattern
        { orPatternSort   :: !(Sort a)
        , orPatternFirst  :: !Pattern
        , orPatternSecond :: !Pattern
        }
    | StringLiteralPattern !StringLiteral
    | forall a . TopPattern !(Sort a)
    | forall a . VariablePattern !(Variable a)

data Sentence
    = forall a . AliasSentence
        { aliasSentenceAlias      :: !(Alias a)
        , aliasSentenceSorts      :: ![Sort a]
        , aliasSentenceReturnSort :: !(Sort a)
        , aliasSentenceAttributes :: !Attributes
        }
    | AxiomSentence
        { axiomSentenceParameters :: ![UnifiedSortVariable]
        , axiomSentencePattern    :: !Pattern
        , axiomSentenceAtrributes :: !Attributes
        }
    | SortSentence
        { sortSentenceParameters :: ![UnifiedSortVariable]
        , sortSentenceSort       :: !(Sort Object)
        , sortSentenceAttributes :: !Attributes
        }
    | forall a. SymbolSentence
        { symbolSentenceSymbol     :: !(Symbol a)
        , symbolSentenceSorts      :: ![Sort a]
        , symbolSentenceReturnSort :: !(Sort a)
        , symbolSentenceAttributes :: !Attributes
        }

newtype Attributes = Attributes { getAttributes :: [Pattern] }

data Module = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![Sentence]
    , moduleAttributes :: !Attributes
    }

data Definition = Definition
    { definitionAttributes :: !Attributes
    , definitionModules    :: !Module
    }
