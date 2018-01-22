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

{-|'Id' corresponds to the @object-identifier@ and @meta-identifier@
syntactic categories from the Semantics of K, Section 9.1.1 (Lexicon).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
newtype Id a = Id { getId :: String }
    deriving (Show, Eq, Typeable)

{-|'StringLiteral' corresponds to the @string@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq)

{-|'SymbolOrAlias' corresponds to the @head{sort-list}@ branch of the
@object-head@ and @meta-head@ syntactic categories from the Semantics of K,
Section 9.1.3 (Heads).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
data SymbolOrAlias a = SymbolOrAlias
    { symbolOrAliasConstructor :: !(Id a)
    , symbolOrAliasParams      :: ![Sort a]
    }
    deriving (Show, Eq, Typeable)

{-|'Symbol' corresponds to the @head(sort-list)@ part of the
@object-symbol-declaration@ and @meta-symbol-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Symbol a = Symbol
    { symbolConstructor :: !(Id a)
    , symbolParams      :: ![Sort a]
    }
    deriving (Show, Eq, Typeable)

{-|'Alias' corresponds to the @head(sort-list)@ part of the
@object-alias-declaration@ and @meta-alias-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Alias a = Alias
    { aliasConstructor :: !(Id a)
    , aliasParams      :: ![Sort a]
    }
    deriving (Show, Eq, Typeable)

{-|'SortVariable' corresponds to the @object-sort-variable@ and
@meta-sort-variable@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
newtype SortVariable a = SortVariable
    { getSortVariable  :: Id a }
    deriving (Show, Eq, Typeable)

{-|'SortActual' corresponds to the @sort-constructor{sort-list}@ branch of the
@object-sort@ and @meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
data SortActual a = SortActual
    { sortActualName  :: !(Id a)
    , sortActualSorts :: ![Sort a]
    }
    deriving (Show, Eq, Typeable)

{-|'Sort' corresponds to the @object-sort@ and
@meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
data Sort a
    = SortVariableSort !(SortVariable a)
    | SortActualSort !(SortActual a)
    deriving (Show, Eq, Typeable)

{-|'MetaSortType' corresponds to the @meta-sort-constructor@ syntactic category
from the Semantics of K, Section 9.1.2 (Sorts).

Ths is not represented directly in the AST, we're using the string
representation instead.
-}
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

{-|'UnifiedSortVariable' corresponds to the @variable@ syntactic category
from the Semantics of K, Section 9.1.2 (Sorts).
-}
data UnifiedSortVariable
    = ObjectSortVariable !(SortVariable Object)
    | MetaSortVariable !(SortVariable Meta)
    deriving (Show, Eq)

{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq)

{-|'Variable' corresponds to the @object-variable@ and
@meta-variable@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
data Variable a = Variable
    { variableName :: !(Id a)
    , variableSort :: !(Sort a)
    }
    deriving (Show, Eq, Typeable)

{-|'UnifiedVariable' corresponds to the @variable@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
data UnifiedVariable
    = MetaVariable !(Variable Meta)
    | ObjectVariable !(Variable Object)
    deriving (Eq, Show)

{-|'UnifiedPattern' corresponds to the @pattern@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
data UnifiedPattern
    = MetaPattern !(Pattern Meta)
    | ObjectPattern !(Pattern Object)
    deriving (Eq, Show)

{-|'And' corresponds to the @\and@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'andSort' is both the sort of the operands and the sort of the result.

This represents the 'andFirst ∧ andSecond' Matching Logic construct.
-}
data And a = And
    { andSort   :: !(Sort a)
    , andFirst  :: !UnifiedPattern
    , andSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Application' corresponds to the @head(pattern-list)@ branches of the
@object-pattern@ and @meta-pattern@ syntactic categories from
the Semantics of K, Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

This represents the σ(φ1, ..., φn) symbol patterns in Matching Logic.
-}
data Application a = Application
    { applicationSymbolOrAlias :: !(SymbolOrAlias a)
    , applicationPatterns      :: ![UnifiedPattern]
    }
    deriving (Eq, Show, Typeable)

{-|'Ceil' corresponds to the @\ceil@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'ceilOperandSort' is the sort of the operand.

'ceilResultSort' is the sort of the result.

This represents the ⌈ceilPattern⌉ Matching Logic construct.
-}
data Ceil a = Ceil
    { ceilOperandSort  :: !(Sort a)
    , ceilResultSort :: !(Sort a)
    , ceilPattern    :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Equals' corresponds to the @\equals@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'equalsOperandSort' is the sort of the operand.

'equalsResultSort' is the sort of the result.

This represents the 'equalsFirst = equalsSecond' Matching Logic construct.
-}
data Equals a = Equals
    { equalsOperandSort  :: !(Sort a)
    , equalsResultSort :: !(Sort a)
    , equalsFirst      :: !UnifiedPattern
    , equalsSecond     :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Exists' corresponds to the @\exists@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'existsSort' is both the sort of the operands and the sort of the result.

This represents the '∃existsVariable(existsPattern)' Matching Logic construct.
-}
data Exists a = Exists
    { existsSort     :: !(Sort a)
    , existsVariable :: !UnifiedVariable
    , existsPattern  :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Floor' corresponds to the @\floor@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'floorOperandSort' is the sort of the operand.

'floorResultSort' is the sort of the result.

This represents the '⌊floorPattern⌋' Matching Logic construct.
-}
data Floor a = Floor
    { floorOperandSort  :: !(Sort a)
    , floorResultSort :: !(Sort a)
    , floorPattern    :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'forallSort' is both the sort of the operands and the sort of the result.

This represents the '∀forallVariable(forallPattern)' Matching Logic construct.
-}
data Forall a = Forall
    { forallSort     :: !(Sort a)
    , forallVariable :: !UnifiedVariable
    , forallPattern  :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Iff' corresponds to the @\iff@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'iffSort' is both the sort of the operands and the sort of the result.

This represents the 'iffFirst ⭤ iffSecond' Matching Logic construct.
-}
data Iff a = Iff
    { iffSort   :: !(Sort a)
    , iffFirst  :: !UnifiedPattern
    , iffSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Implies' corresponds to the @\implies@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'impliesSort' is both the sort of the operands and the sort of the result.

This represents the 'impliesFirst ⭢ impliesSecond' Matching Logic construct.
-}
data Implies a = Implies
    { impliesSort   :: !(Sort a)
    , impliesFirst  :: !UnifiedPattern
    , impliesSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Mem' corresponds to the @\mem@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'memOperandSort' is the sort of the operands.

'memResultSort' is the sort of the result.

This represents the 'memVariable ∊ memPattern' Matching Logic construct.
-}
data Mem a = Mem
    { memOperandSort  :: !(Sort a)
    , memResultSort :: !(Sort a)
    , memVariable   :: !UnifiedVariable
    , memPattern    :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Not' corresponds to the @\not@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'notSort' is both the sort of the operand and the sort of the result.

This represents the '¬ notPattern' Matching Logic construct.
-}
data Not a = Not
    { notSort    :: !(Sort a)
    , notPattern :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Or' corresponds to the @\or@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'orSort' is both the sort of the operands and the sort of the result.

This represents the 'orFirst ∨ orSecond' Matching Logic construct.
-}
data Or a = Or
    { orSort   :: !(Sort a)
    , orFirst  :: !UnifiedPattern
    , orSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Pattern' corresponds to the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

Note that the StringLiteralPattern should only be a member of 'Pattern Meta'.
-}
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

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
data SentenceAlias a = SentenceAlias
    { sentenceAliasAlias      :: !(Alias a)
    , sentenceAliasSorts      :: ![Sort a]
    , sentenceAliasReturnSort :: !(Sort a)
    , sentenceAliasAttributes :: !Attributes
    }
    deriving (Eq, Show, Typeable)

{-|'SentenceSymbol' corresponds to the @object-symbol-declaration@ and
@meta-symbol-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
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
