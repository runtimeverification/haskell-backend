{-|
Module      : KoreAST
Description : Data Structures for representing the Kore language AST
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

This module includes all the data structures necessary for representing
all the syntactic categories of a Kore definition.

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.


-}
module KoreAST where

import Data.Typeable

data MetaType
    = ObjectType
    | MetaType
    deriving (Eq, Show)

class Show a => IsMeta a where
    metaType :: a -> MetaType

data Meta = Meta
    deriving (Show, Eq, Typeable)

instance IsMeta Meta where
    metaType _ = MetaType

data Object = Object
    deriving (Show, Eq, Typeable)

instance IsMeta Object where
    metaType _ = ObjectType

isObject :: (IsMeta a, Typeable (m a)) => m a -> Bool
isObject x = (head $ typeRepArgs (typeOf x)) == typeOf Object

isMeta :: (IsMeta a, Typeable (m a)) => m a -> Bool
isMeta x = (head $ typeRepArgs (typeOf x)) == typeOf Meta

newtype Id a = Id { getId :: String }
    deriving (Show, Eq, Typeable)

newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq)

data SymbolOrAlias a = SymbolOrAlias
    { symbolOrAliasConstructor :: !(Id a)
    , symbolOrAliasParams      :: ![Sort a]
    }
    deriving (Show, Eq, Typeable)

data Symbol a = Symbol
    { symbolConstructor :: !(Id a)
    , symbolParams      :: ![Sort a]
    }
    deriving (Show, Eq, Typeable)

data Alias a = Alias
    { aliasConstructor :: !(Id a)
    , aliasParams      :: ![Sort a]
    }
    deriving (Show, Eq, Typeable)

newtype SortVariable a = SortVariable
    { getSortVariable  :: Id a }
    deriving (Show, Eq, Typeable)

data SortActual a = SortActual
    { sortActualName  :: !(Id a)
    , sortActualSorts :: ![Sort a]
    }
    deriving (Show, Eq, Typeable)

data Sort a
    = SortVariableSort !(SortVariable a)
    | SortActualSort !(SortActual a)
    deriving (Show, Eq, Typeable)

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
    { variableName :: !(Id a)
    , variableSort :: !(Sort a)
    }
    deriving (Show, Eq, Typeable)

data UnifiedVariable
    = MetaVariable !(Variable Meta)
    | ObjectVariable !(Variable Object)
    deriving (Eq, Show)

data UnifiedPattern
    = MetaPattern !(Pattern Meta)
    | ObjectPattern !(Pattern Object)
    deriving (Eq, Show)

data And a = And
    { andSort   :: !(Sort a)
    , andFirst  :: !UnifiedPattern
    , andSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Application a = Application
    { applicationSymbolOrAlias :: !(SymbolOrAlias a)
    , applicationPatterns      :: ![UnifiedPattern]
    }
    deriving (Eq, Show, Typeable)

data Ceil a = Ceil
    { ceilFirstSort  :: !(Sort a)
    , ceilSecondSort :: !(Sort a)
    , ceilPattern    :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Equals a = Equals
    { equalsFirstSort  :: !(Sort a)
    , equalsSecondSort :: !(Sort a)
    , equalsFirst      :: !UnifiedPattern
    , equalsSecond     :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Exists a = Exists
    { existsSort     :: !(Sort a)
    , existsVariable :: !UnifiedVariable
    , existsPattern  :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Floor a = Floor
    { floorFirstSort  :: !(Sort a)
    , floorSecondSort :: !(Sort a)
    , floorPattern    :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Forall a = Forall
    { forallSort     :: !(Sort a)
    , forallVariable :: !UnifiedVariable
    , forallPattern  :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Iff a = Iff
    { iffSort   :: !(Sort a)
    , iffFirst  :: !UnifiedPattern
    , iffSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Implies a = Implies
    { impliesSort   :: !(Sort a)
    , impliesFirst  :: !UnifiedPattern
    , impliesSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Mem a = Mem
    { memFirstSort  :: !(Sort a)
    , memSecondSort :: !(Sort a)
    , memVariable   :: !UnifiedVariable
    , memPattern    :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Not a = Not
    { notSort    :: !(Sort a)
    , notPattern :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Or a = Or
    { orSort   :: !(Sort a)
    , orFirst  :: !UnifiedPattern
    , orSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

data Pattern a
    = AndPattern !(And a)
    | ApplicationPattern !(Application a)
    | BottomPattern !(Sort a)
    | CeilPattern !(Ceil a)
    | EqualsPattern !(Equals a)
    | ExistsPattern !(Exists a)
    | FloorPattern !(Floor a)
    | ForallPattern !(Forall a)
    | IffPattern !(Iff a)
    | ImpliesPattern !(Implies a)
    | MemPattern !(Mem a)
    | NotPattern !(Not a)
    | OrPattern !(Or a)
    | StringLiteralPattern !StringLiteral
    | TopPattern !(Sort a)
    | VariablePattern !(Variable a)
    deriving (Eq, Show, Typeable)

data SentenceAlias a = SentenceAlias
    { sentenceAliasAlias      :: !(Alias a)
    , sentenceAliasSorts      :: ![Sort a]
    , sentenceAliasReturnSort :: !(Sort a)
    , sentenceAliasAttributes :: !Attributes
    }
    deriving (Eq, Show, Typeable)

data SentenceSymbol a = SentenceSymbol
    { sentenceSymbolSymbol     :: !(Symbol a)
    , sentenceSymbolSorts      :: ![Sort a]
    , sentenceSymbolReturnSort :: !(Sort a)
    , sentenceSymbolAttributes :: !Attributes
    }
    deriving (Eq, Show, Typeable)

{-|'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceAxiom = SentenceAxiom
    { sentenceAxiomParameters :: ![UnifiedSortVariable]
    , sentenceAxiomPattern    :: !UnifiedPattern
    , sentenceAxiomAtrributes :: !Attributes
    }
    deriving (Eq, Show)

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort = SentenceSort
    { sentenceSortParameters :: ![UnifiedSortVariable]
    , sentenceSortSort       :: !(Sort Object)
    , sentenceSortAttributes :: !Attributes
    }
    deriving (Eq, Show)

{-|The 'Sentence' type corresponds to the @declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The @symbol-declaration@ and @alias-declaration@ categories were also merged
into 'Sentence', with distinct constructors for the @Meta@ and @Object@
variants.
-}
data Sentence
    = MetaSentenceAliasSentence !(SentenceAlias Meta)
    | ObjectSentenceAliasSentence !(SentenceAlias Object)
    | MetaSentenceSymbolSentence !(SentenceSymbol Meta)
    | ObjectSentenceSymbolSentence !(SentenceSymbol Object)
    | SentenceAxiomSentence !SentenceAxiom
    | SentenceSortSentence !SentenceSort
    deriving (Eq, Show)

newtype Attributes = Attributes { getAttributes :: [UnifiedPattern] }
    deriving (Eq, Show)

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![Sentence]
    , moduleAttributes :: !Attributes
    }
    deriving (Eq, Show)

{-|Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition = Definition
    { definitionAttributes :: !Attributes
    , definitionModules    :: !Module
    }
    deriving (Eq, Show)
