{-|
Module      : Data.Kore.AST
Description : Data Structures for representing the Kore language AST
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module includes all the data structures necessary for representing
all the syntactic categories of a Kore definition.

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.


-}
module Data.Kore.AST where

import           Data.Typeable (Typeable, typeOf, typeRepArgs)

data KoreLevel
    = ObjectLevel
    | MetaLevel
    deriving (Eq, Show)

class (Show a, Typeable a) => IsMeta a where
    koreLevel :: a -> KoreLevel

data Meta = Meta
    deriving (Show, Eq, Typeable)

instance IsMeta Meta where
    koreLevel _ = MetaLevel

data Object = Object
    deriving (Show, Eq, Typeable)

instance IsMeta Object where
    koreLevel _ = ObjectLevel

isObject :: (IsMeta a, Typeable (m a)) => m a -> Bool
isObject x = head (typeRepArgs (typeOf x)) == typeOf Object

isMeta :: (IsMeta a, Typeable (m a)) => m a -> Bool
isMeta x = head (typeRepArgs (typeOf x)) == typeOf Meta

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

{-|'Symbol' corresponds to the
@object-head-constructor{object-sort-variable-list}@ part of the
@object-symbol-declaration@ and @meta-symbol-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Symbol a = Symbol
    { symbolConstructor :: !(Id a)
    , symbolParams      :: ![SortVariable a]
    }
    deriving (Show, Eq, Typeable)

{-|'Alias' corresponds to the
@object-head-constructor{object-sort-variable-list}@ part of the
@object-alias-declaration@ and @meta-alias-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Alias a = Alias
    { aliasConstructor :: !(Id a)
    , aliasParams      :: ![SortVariable a]
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

metaSortsList :: [MetaSortType]
metaSortsList = [ CharSort, CharListSort, PatternSort, PatternListSort, SortSort
    , SortListSort, StringSort, SymbolSort, SymbolListSort
    , VariableSort, VariableListSort
    ]

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

{-|Enumeration of patterns starting with @\@
-}
data MLPatternType
    = AndPatternType
    | BottomPatternType
    | CeilPatternType
    | EqualsPatternType
    | ExistsPatternType
    | FloorPatternType
    | ForallPatternType
    | IffPatternType
    | ImpliesPatternType
    | InPatternType
    | NextPatternType
    | NotPatternType
    | OrPatternType
    | RewritesPatternType
    | TopPatternType
    deriving Show

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

{-|'Bottom' corresponds to the @\bottom@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'bottomSort' is the sort of the result.

This represents the ⌈BottomPattern⌉ Matching Logic construct.
-}
newtype Bottom a = Bottom { bottomSort :: Sort a}
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
    { ceilOperandSort :: !(Sort a)
    , ceilResultSort  :: !(Sort a)
    , ceilPattern     :: !UnifiedPattern
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
    { equalsOperandSort :: !(Sort a)
    , equalsResultSort  :: !(Sort a)
    , equalsFirst       :: !UnifiedPattern
    , equalsSecond      :: !UnifiedPattern
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
    { floorOperandSort :: !(Sort a)
    , floorResultSort  :: !(Sort a)
    , floorPattern     :: !UnifiedPattern
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

{-|'In' corresponds to the @\in@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'inOperandSort' is the sort of the operands.

'inResultSort' is the sort of the result.

This represents the 'inMemberPattern ∊ inContainingPattern' Matching Logic
construct, which, when 'inMemberPattern' is a singleton (e.g. a variable),
represents the set membership. However, in general, it actually means that the
two patterns have a non-empty intersection.
-}
data In a = In
    { inOperandSort       :: !(Sort a)
    , inResultSort        :: !(Sort a)
    , inContainedPattern  :: !UnifiedPattern
    , inContainingPattern :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)


{-|'Next' corresponds to the @\next@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

Although there is no 'meta' version of @\next@, there is an 'a' type parameter
which should verify 'IsMeta a'. The object-only restriction is done at the
Pattern level.

'nextSort' is both the sort of the operand and the sort of the result.

This represents the '∘ nextPattern' Matching Logic construct.
-}
data Next a = Next
    { nextSort    :: !(Sort a)
    , nextPattern :: !UnifiedPattern
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

{-|'Rewrites' corresponds to the @\rewrites@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

Although there is no 'meta' version of @\rewrites@, there is an 'a' type
parameter which should verify 'IsMeta a'. The object-only restriction is
done at the Pattern level.

'rewritesSort' is both the sort of the operands and the sort of the result.

This represents the 'rewritesFirst ⇒ rewritesSecond' Matching Logic construct.
-}

data Rewrites a = Rewrites
    { rewritesSort   :: !(Sort a)
    , rewritesFirst  :: !UnifiedPattern
    , rewritesSecond :: !UnifiedPattern
    }
    deriving (Eq, Show, Typeable)

{-|'Top' corresponds to the @\top@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'topSort' is the sort of the result.

This represents the ⌈TopPattern⌉ Matching Logic construct.
-}
newtype Top a = Top { topSort :: Sort a}
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
    | BottomPattern !(Bottom a)
    | CeilPattern !(Ceil a)
    | EqualsPattern !(Equals a)
    | ExistsPattern !(Exists a)
    | FloorPattern !(Floor a)
    | ForallPattern !(Forall a)
    | IffPattern !(Iff a)
    | ImpliesPattern !(Implies a)
    | InPattern !(In a)
    | NextPattern !(Next Object)
    | NotPattern !(Not a)
    | OrPattern !(Or a)
    | RewritesPattern !(Rewrites Object)
    | StringLiteralPattern !StringLiteral
    | TopPattern !(Top a)
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
    , sentenceAxiomAttributes :: !Attributes
    }
    deriving (Eq, Show)

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort = SentenceSort
    { sentenceSortName       :: !(Id Object)
    , sentenceSortParameters :: ![SortVariable Object]
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

class AsPattern t where
    asPattern :: t a -> Pattern a

instance AsPattern And where
    asPattern = AndPattern

instance AsPattern Bottom where
    asPattern = BottomPattern

instance AsPattern Ceil where
    asPattern = CeilPattern

instance AsPattern Equals where
    asPattern = EqualsPattern

instance AsPattern Exists where
    asPattern = ExistsPattern

instance AsPattern Floor where
    asPattern = FloorPattern

instance AsPattern Forall where
    asPattern = ForallPattern

instance AsPattern Iff where
    asPattern = IffPattern

instance AsPattern Implies where
    asPattern = ImpliesPattern

instance AsPattern In where
    asPattern = InPattern

instance AsPattern Not where
    asPattern = NotPattern

instance AsPattern Or where
    asPattern = OrPattern

instance AsPattern Top where
    asPattern = TopPattern

instance AsPattern Variable where
    asPattern = VariablePattern


class AsObjectPattern t where
    asObjectPattern :: t Object -> Pattern Object

instance AsObjectPattern Next where
    asObjectPattern = NextPattern

instance AsObjectPattern Rewrites where
    asObjectPattern = RewritesPattern

{-|'MLPatternClass' offers a common interface to ML patterns
  (those starting with '\', except for 'Exists' and 'Forall')
-}
class MLPatternClass p where
    getPatternType :: p a -> MLPatternType
    getPatternSorts :: p a -> [Sort a]
    getPatternPatterns :: p a -> [UnifiedPattern]

instance MLPatternClass And where
    getPatternType _ = AndPatternType
    getPatternSorts a = [andSort a]
    getPatternPatterns a = [andFirst a, andSecond a]

instance MLPatternClass Bottom where
    getPatternType _ = BottomPatternType
    getPatternSorts b = [bottomSort b]
    getPatternPatterns _ = []

instance MLPatternClass Ceil where
    getPatternType _ = CeilPatternType
    getPatternSorts c = [ceilOperandSort c, ceilResultSort c]
    getPatternPatterns c = [ceilPattern c]

instance MLPatternClass Equals where
    getPatternType _ = EqualsPatternType
    getPatternSorts e = [equalsOperandSort e, equalsResultSort e]
    getPatternPatterns e = [equalsFirst e, equalsSecond e]

instance MLPatternClass Floor where
    getPatternType _ = FloorPatternType
    getPatternSorts f = [floorOperandSort f, floorResultSort f]
    getPatternPatterns f = [floorPattern f]

instance MLPatternClass Iff where
    getPatternType _ = IffPatternType
    getPatternSorts i = [iffSort i]
    getPatternPatterns i = [iffFirst i, iffSecond i]

instance MLPatternClass Implies where
    getPatternType _ = ImpliesPatternType
    getPatternSorts i = [impliesSort i]
    getPatternPatterns i = [impliesFirst i, impliesSecond i]

instance MLPatternClass In where
    getPatternType _ = InPatternType
    getPatternSorts i = [inOperandSort i, inResultSort i]
    getPatternPatterns i = [inContainedPattern i, inContainingPattern i]

instance MLPatternClass Next where
    getPatternType _ = NextPatternType
    getPatternSorts e = [nextSort e]
    getPatternPatterns e = [nextPattern e]

instance MLPatternClass Not where
    getPatternType _ = NotPatternType
    getPatternSorts n = [notSort n]
    getPatternPatterns n = [notPattern n]

instance MLPatternClass Or where
    getPatternType _ = OrPatternType
    getPatternSorts a = [orSort a]
    getPatternPatterns a = [orFirst a, orSecond a]

instance MLPatternClass Rewrites where
    getPatternType _ = RewritesPatternType
    getPatternSorts e = [rewritesSort e]
    getPatternPatterns e = [rewritesFirst e, rewritesSecond e]

instance MLPatternClass Top where
    getPatternType _ = TopPatternType
    getPatternSorts t = [topSort t]
    getPatternPatterns _ = []

class MLBinderPatternClass p where
    getBinderPatternType :: p a -> MLPatternType
    getBinderPatternSort :: p a -> Sort a
    getBinderPatternVariable :: p a -> UnifiedVariable
    getBinderPatternPattern :: p a -> UnifiedPattern

instance MLBinderPatternClass Exists where
    getBinderPatternType _ = ExistsPatternType
    getBinderPatternSort = existsSort
    getBinderPatternVariable = existsVariable
    getBinderPatternPattern = existsPattern

instance MLBinderPatternClass Forall where
    getBinderPatternType _ = ForallPatternType
    getBinderPatternSort = forallSort
    getBinderPatternVariable = forallVariable
    getBinderPatternPattern = forallPattern
