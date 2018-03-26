{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-|
Module      : Data.Kore.AST.Common
Description : Data Structures for representing the Kore language AST that do not
              need unified constructs (see Data.Kore.AST.Kore for the unified
              ones).
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that do not need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort Object' or 'Sort Meta')

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}
module Data.Kore.AST.Common where

import           Data.Typeable (Typeable)

data Meta = Meta
    deriving (Show, Eq, Ord, Typeable)

data Object = Object
    deriving (Show, Eq, Ord, Typeable)

{-|'Id' corresponds to the @object-identifier@ and @meta-identifier@
syntactic categories from the Semantics of K, Section 9.1.1 (Lexicon).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

We may chage the Id's representation in the future so one should treat it as
an opaque entity as much as possible.
-}
newtype Id level = Id { getId :: String }
    deriving (Show, Eq, Ord, Typeable)

{-|'StringLiteral' corresponds to the @string@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq, Ord)

{-|'CharLiteral' corresponds to the @char@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype CharLiteral = CharLiteral { getCharLiteral :: Char }
    deriving (Show, Eq, Ord)

{-|'SymbolOrAlias' corresponds to the @head{sort-list}@ branch of the
@object-head@ and @meta-head@ syntactic categories from the Semantics of K,
Section 9.1.3 (Heads).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SymbolOrAlias level = SymbolOrAlias
    { symbolOrAliasConstructor :: !(Id level)
    , symbolOrAliasParams      :: ![Sort level]
    }
    deriving (Show, Eq, Ord, Typeable)

{-|'Symbol' corresponds to the
@object-head-constructor{object-sort-variable-list}@ part of the
@object-symbol-declaration@ and @meta-symbol-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Symbol level = Symbol
    { symbolConstructor :: !(Id level)
    , symbolParams      :: ![SortVariable level]
    }
    deriving (Show, Eq, Ord, Typeable)

{-|'Alias' corresponds to the
@object-head-constructor{object-sort-variable-list}@ part of the
@object-alias-declaration@ and @meta-alias-declaration@ syntactic categories
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that this is very similar to 'SymbolOrAlias'.
-}
data Alias level = Alias
    { aliasConstructor :: !(Id level)
    , aliasParams      :: ![SortVariable level]
    }
    deriving (Show, Eq, Ord, Typeable)

{-|'SortVariable' corresponds to the @object-sort-variable@ and
@meta-sort-variable@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
newtype SortVariable level = SortVariable
    { getSortVariable  :: Id level }
    deriving (Show, Eq, Ord, Typeable)

{-|'SortActual' corresponds to the @sort-constructor{sort-list}@ branch of the
@object-sort@ and @meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SortActual level = SortActual
    { sortActualName  :: !(Id level)
    , sortActualSorts :: ![Sort level]
    }
    deriving (Show, Eq, Ord, Typeable)

{-|'Sort' corresponds to the @object-sort@ and
@meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data Sort level
    = SortVariableSort !(SortVariable level)
    | SortActualSort !(SortActual level)
    deriving (Show, Eq, Ord, Typeable)

{-|'MetaSortType' corresponds to the @meta-sort-constructor@ syntactic category
from the Semantics of K, Section 9.1.2 (Sorts).

Ths is not represented directly in the AST, we're using the string
representation instead.
-}
data MetaBasicSortType
    = CharSort
    | PatternSort
    | SortSort
    | SymbolSort
    | VariableSort

data MetaSortType
    = MetaBasicSortType MetaBasicSortType
    | MetaListSortType MetaBasicSortType
    | StringSort

metaBasicSortsList :: [MetaBasicSortType]
metaBasicSortsList =
    [ CharSort
    , PatternSort
    , SortSort
    , SymbolSort
    , VariableSort
    ]

metaSortsList :: [MetaSortType]
metaSortsList =
    map MetaBasicSortType metaBasicSortsList
    ++ map MetaListSortType metaBasicSortsList

metaSortsListWithString :: [MetaSortType]
metaSortsListWithString = StringSort : metaSortsList

metaBasicSortTypeString :: MetaBasicSortType -> String
metaBasicSortTypeString CharSort     = "Char"
metaBasicSortTypeString PatternSort  = "Pattern"
metaBasicSortTypeString SortSort     = "Sort"
metaBasicSortTypeString SymbolSort   = "Symbol"
metaBasicSortTypeString VariableSort = "Variable"

metaSortTypeString :: MetaSortType -> String
metaSortTypeString (MetaBasicSortType s) = metaBasicSortTypeString s
metaSortTypeString (MetaListSortType s)  =
    metaBasicSortTypeString s ++ "List"
metaSortTypeString StringSort            = "String"

instance Show MetaSortType where
    show sortType = '#' : metaSortTypeString sortType

{-|'Variable' corresponds to the @object-variable@ and
@meta-variable@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data Variable level = Variable
    { variableName :: !(Id level)
    , variableSort :: !(Sort level)
    }
    deriving (Show, Eq, Ord, Typeable)

{-|Enumeration of patterns starting with @\@
-}
data MLPatternType
    = AndPatternType
    | BottomPatternType
    | CeilPatternType
    | DomainValuePatternType
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

allPatternTypes :: [MLPatternType]
allPatternTypes =
    [ AndPatternType
    , BottomPatternType
    , CeilPatternType
    , DomainValuePatternType
    , EqualsPatternType
    , ExistsPatternType
    , FloorPatternType
    , ForallPatternType
    , IffPatternType
    , ImpliesPatternType
    , InPatternType
    , NextPatternType
    , NotPatternType
    , OrPatternType
    , RewritesPatternType
    , TopPatternType
    ]

patternString :: MLPatternType -> String
patternString pt = case pt of
    AndPatternType         -> "and"
    BottomPatternType      -> "bottom"
    CeilPatternType        -> "ceil"
    DomainValuePatternType -> "dv"
    EqualsPatternType      -> "equals"
    ExistsPatternType      -> "exists"
    FloorPatternType       -> "floor"
    ForallPatternType      -> "forall"
    IffPatternType         -> "iff"
    ImpliesPatternType     -> "implies"
    InPatternType          -> "in"
    NextPatternType        -> "next"
    NotPatternType         -> "not"
    OrPatternType          -> "or"
    RewritesPatternType    -> "rewrites"
    TopPatternType         -> "top"

{-|'And' corresponds to the @\and@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'andSort' is both the sort of the operands and the sort of the result.

This represents the 'andFirst ∧ andSecond' Matching Logic construct.
-}
data And level p = And
    { andSort   :: !(Sort level)
    , andFirst  :: !p
    , andSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Application' corresponds to the @head(pattern-list)@ branches of the
@object-pattern@ and @meta-pattern@ syntactic categories from
the Semantics of K, Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

This represents the σ(φ1, ..., φn) symbol patterns in Matching Logic.
-}
data Application level p = Application
    { applicationSymbolOrAlias :: !(SymbolOrAlias level)
    , applicationChildren      :: ![p]
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Bottom' corresponds to the @\bottom@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'bottomSort' is the sort of the result.

This represents the ⌈BottomPattern⌉ Matching Logic construct.
-}
newtype Bottom level p = Bottom { bottomSort :: Sort level}
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Ceil' corresponds to the @\ceil@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'ceilOperandSort' is the sort of the operand.

'ceilResultSort' is the sort of the result.

This represents the ⌈ceilPattern⌉ Matching Logic construct.
-}
data Ceil level p = Ceil
    { ceilOperandSort :: !(Sort level)
    , ceilResultSort  :: !(Sort level)
    , ceilChild       :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'DomainValue' corresponds to the @\dv@ branch of the @object-pattern@
syntactic category, which are not yet in the Semantics of K document,
but they should appear in Section 9.1.4 (Patterns) at some point.

Although there is no 'Meta' version of 'DomainValue's, for uniformity,
the 'level' type parameter is used to distiguish between the hypothetical
meta- and object- versions of symbol declarations. It should verify
'MetaOrObject level'.

'domainValueSort' is the sort of the result.

This represents the encoding of an object constant, e.g. we may use
\dv{Int{}}{"123"} instead of a representation based on constructors,
e.g. succesor(succesor(...succesor(0)...))
-}
data DomainValue level p = DomainValue
    { domainValueSort  :: !(Sort level)
    , domainValueChild :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Equals' corresponds to the @\equals@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'equalsOperandSort' is the sort of the operand.

'equalsResultSort' is the sort of the result.

This represents the 'equalsFirst = equalsSecond' Matching Logic construct.
-}
data Equals level p = Equals
    { equalsOperandSort :: !(Sort level)
    , equalsResultSort  :: !(Sort level)
    , equalsFirst       :: !p
    , equalsSecond      :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Exists' corresponds to the @\exists@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'existsSort' is both the sort of the operands and the sort of the result.

This represents the '∃existsVariable(existsChild)' Matching Logic construct.
-}
data Exists level v p = Exists
    { existsSort     :: !(Sort level)
    , existsVariable :: !(v level)
    , existsChild    :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Floor' corresponds to the @\floor@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'floorOperandSort' is the sort of the operand.

'floorResultSort' is the sort of the result.

This represents the '⌊floorPattern⌋' Matching Logic construct.
-}
data Floor level p = Floor
    { floorOperandSort :: !(Sort level)
    , floorResultSort  :: !(Sort level)
    , floorChild       :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'forallSort' is both the sort of the operands and the sort of the result.

This represents the '∀forallVariable(forallChild)' Matching Logic construct.
-}
data Forall level v p = Forall
    { forallSort     :: !(Sort level)
    , forallVariable :: !(v level)
    , forallChild    :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Iff' corresponds to the @\iff@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'iffSort' is both the sort of the operands and the sort of the result.

This represents the 'iffFirst ⭤ iffSecond' Matching Logic construct.
-}
data Iff level p = Iff
    { iffSort   :: !(Sort level)
    , iffFirst  :: !p
    , iffSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Implies' corresponds to the @\implies@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'impliesSort' is both the sort of the operands and the sort of the result.

This represents the 'impliesFirst ⭢ impliesSecond' Matching Logic construct.
-}
data Implies level p = Implies
    { impliesSort   :: !(Sort level)
    , impliesFirst  :: !p
    , impliesSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'In' corresponds to the @\in@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'inOperandSort' is the sort of the operands.

'inResultSort' is the sort of the result.

This represents the 'inContainedChild ∊ inContainingChild' Matching Logic
construct, which, when 'inContainedChild' is a singleton (e.g. a variable),
represents the set membership. However, in general, it actually means that the
two patterns have a non-empty intersection.
-}
data In level p = In
    { inOperandSort     :: !(Sort level)
    , inResultSort      :: !(Sort level)
    , inContainedChild  :: !p
    , inContainingChild :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)


{-|'Next' corresponds to the @\next@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

Although there is no 'meta' version of @\next@, there is a 'level' type
parameter which will always be 'Object'. The object-only restriction is
done at the 'Pattern' level.

'nextSort' is both the sort of the operand and the sort of the result.

This represents the '∘ nextChild' Matching Logic construct.
-}
data Next level p = Next
    { nextSort  :: !(Sort level)
    , nextChild :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Not' corresponds to the @\not@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'notSort' is both the sort of the operand and the sort of the result.

This represents the '¬ notChild' Matching Logic construct.
-}
data Not level p = Not
    { notSort  :: !(Sort level)
    , notChild :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Or' corresponds to the @\or@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'orSort' is both the sort of the operands and the sort of the result.

This represents the 'orFirst ∨ orSecond' Matching Logic construct.
-}
data Or level p = Or
    { orSort   :: !(Sort level)
    , orFirst  :: !p
    , orSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Rewrites' corresponds to the @\rewrites@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

Although there is no 'Meta' version of @\rewrites@, there is a 'level' type
parameter which will always be 'Object'. The object-only restriction is
done at the Pattern level.

'rewritesSort' is both the sort of the operands and the sort of the result.

This represents the 'rewritesFirst ⇒ rewritesSecond' Matching Logic construct.
-}

data Rewrites level p = Rewrites
    { rewritesSort   :: !(Sort level)
    , rewritesFirst  :: !p
    , rewritesSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Top' corresponds to the @\top@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'topSort' is the sort of the result.

This represents the ⌈TopPattern⌉ Matching Logic construct.
-}
newtype Top level p = Top { topSort :: Sort level}
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Pattern' corresponds to the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that the 'StringLiteralPattern' and 'CharLiteralPattern' should
be members only of 'Pattern Meta'.
-}
data Pattern level variable child where
    AndPattern
        :: !(And level child) -> Pattern level variable child
    ApplicationPattern
        :: !(Application level child) -> Pattern level variable child
    BottomPattern
        :: !(Bottom level child) -> Pattern level variable child
    CeilPattern
        :: !(Ceil level child) -> Pattern level variable child
    DomainValuePattern
        :: !(DomainValue Object child) -> Pattern Object variable child
    EqualsPattern
        :: !(Equals level child) -> Pattern level variable child
    ExistsPattern
        :: !(Exists level variable child) -> Pattern level variable child
    FloorPattern
        :: !(Floor level child) -> Pattern level variable child
    ForallPattern
        :: !(Forall level variable child) -> Pattern level variable child
    IffPattern
        :: !(Iff level child) -> Pattern level variable child
    ImpliesPattern
        :: !(Implies level child) -> Pattern level variable child
    InPattern
        :: !(In level child) -> Pattern level variable child
    NextPattern
        :: !(Next Object child) -> Pattern Object variable child
    NotPattern
        :: !(Not level child) -> Pattern level variable child
    OrPattern
        :: !(Or level child) -> Pattern level variable child
    RewritesPattern
        :: !(Rewrites Object child) -> Pattern Object variable child
    StringLiteralPattern
        :: !StringLiteral -> Pattern Meta variable child
    CharLiteralPattern
        :: !CharLiteral -> Pattern Meta variable child
    TopPattern
        :: !(Top level child) -> Pattern level variable child
    VariablePattern
        :: !(variable level) -> Pattern level variable child
  deriving (Typeable)

deriving instance
    ( Eq child
    , Eq (variable level)
    ) => Eq (Pattern level variable child)
deriving instance
    ( Show child
    , Show (variable level)
    ) => Show (Pattern level variable child)
deriving instance Functor (Pattern level variable)
deriving instance Foldable (Pattern level variable)
deriving instance Traversable (Pattern level variable)

{-|'Attributes' corresponds to the @attributes@ Kore syntactic declaration.
It is parameterized by the types of Patterns, @pat@.
-}
newtype Attributes pat (variable :: * -> *) =
    Attributes { getAttributes :: [pat variable] }
  deriving (Eq, Show)

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceAlias level pat variable = SentenceAlias
    { sentenceAliasAlias      :: !(Alias level)
    , sentenceAliasSorts      :: ![Sort level]
    , sentenceAliasResultSort :: !(Sort level)
    , sentenceAliasAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show, Typeable)

{-|'SentenceSymbol' corresponds to the @object-symbol-declaration@ and
@meta-symbol-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data SentenceSymbol level pat variable = SentenceSymbol
    { sentenceSymbolSymbol     :: !(Symbol level)
    , sentenceSymbolSorts      :: ![Sort level]
    , sentenceSymbolResultSort :: !(Sort level)
    , sentenceSymbolAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show, Typeable)

{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq, Ord)

{-|'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceImport pat variable = SentenceImport
    { sentenceImportModuleName :: !ModuleName
    , sentenceImportAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show, Typeable)

{-|'SentenceSort' corresponds to the @sort-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceSort level pat variable = SentenceSort
    { sentenceSortName       :: !(Id level)
    , sentenceSortParameters :: ![SortVariable level]
    , sentenceSortAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show)

{-|'SentenceAxiom' corresponds to the @axiom-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceAxiom sortParam pat variable = SentenceAxiom
    { sentenceAxiomParameters :: ![sortParam]
    , sentenceAxiomPattern    :: !(pat variable)
    , sentenceAxiomAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show)

{-|The 'Sentence' type corresponds to the @declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).

The @symbol-declaration@ and @alias-declaration@ categories were also merged
into 'Sentence', using the @level@ parameter to distinguish the 'Meta' and
'Object' variants.
Since axioms and imports exist at both meta and kore levels, we use 'Meta'
to qualify them. In contrast, since sort declarations are not available
at the meta level, we qualify them with 'Object'.
-}
data Sentence level sortParam pat variable where
    SentenceAliasSentence
        :: !(SentenceAlias level pat variable)
        -> Sentence level sortParam pat variable
    SentenceSymbolSentence
        :: !(SentenceSymbol level pat variable)
        -> Sentence level sortParam pat variable
    SentenceImportSentence
        :: !(SentenceImport pat variable)
        -> Sentence Meta sortParam pat variable
    SentenceAxiomSentence
        :: !(SentenceAxiom sortParam pat variable)
        -> Sentence Meta sortParam pat variable
    SentenceSortSentence
        :: !(SentenceSort Object pat variable)
        -> Sentence Object sortParam pat variable

deriving instance
    ( Eq (pat variable)
    , Eq sortParam
    ) => Eq (Sentence level sortParam pat variable)
deriving instance
    ( Show (pat variable)
    , Show sortParam
    ) => Show (Sentence level sortParam pat variable)

{-|A 'Module' consists of a 'ModuleName' a list of 'Sentence's and some
'Attributes'.

They correspond to the second, third and forth non-terminals of the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions).
-}
data Module sentence sortParam pat variable = Module
    { moduleName       :: !ModuleName
    , moduleSentences  :: ![sentence sortParam pat variable]
    , moduleAttributes :: !(Attributes pat variable)
    }
    deriving (Eq, Show)

{-|Currently, a 'Definition' consists of some 'Attributes' and a 'Module'

Because there are plans to extend this to a list of 'Module's, the @definition@
syntactic category from the Semantics of K, Section 9.1.6
(Declaration and Definitions) is splitted here into 'Definition' and 'Module'.

'definitionAttributes' corresponds to the first non-terminal of @definition@,
while the remaining three are grouped into 'definitionModules'.
-}
data Definition sentence sortParam pat variable = Definition
    { definitionAttributes :: !(Attributes pat variable)
    , definitionModules    :: ![Module sentence sortParam pat variable]
    }
    deriving (Eq, Show)

class SentenceSymbolOrAlias sentence where
    getSentenceSymbolOrAliasConstructor
        :: sentence level pat variable -> Id level
    getSentenceSymbolOrAliasSortParams
        :: sentence level pat variable -> [SortVariable level]
    getSentenceSymbolOrAliasArgumentSorts
        :: sentence level pat variable -> [Sort level]
    getSentenceSymbolOrAliasResultSort
        :: sentence level pat variable -> Sort level
    getSentenceSymbolOrAliasAttributes
        :: sentence level pat variable -> Attributes pat variable
    getSentenceSymbolOrAliasSentenceName
        :: sentence level pat variable -> String
    getSentenceSymbolOrAliasHead
        :: sentence level pat variable -> [Sort level] -> SymbolOrAlias level
    getSentenceSymbolOrAliasHead sentence sortParameters = SymbolOrAlias
        { symbolOrAliasConstructor =
            getSentenceSymbolOrAliasConstructor sentence
        , symbolOrAliasParams = sortParameters
        }

instance SentenceSymbolOrAlias SentenceAlias where
    getSentenceSymbolOrAliasConstructor = aliasConstructor . sentenceAliasAlias
    getSentenceSymbolOrAliasSortParams = aliasParams . sentenceAliasAlias
    getSentenceSymbolOrAliasArgumentSorts = sentenceAliasSorts
    getSentenceSymbolOrAliasResultSort = sentenceAliasResultSort
    getSentenceSymbolOrAliasAttributes = sentenceAliasAttributes
    getSentenceSymbolOrAliasSentenceName _ = "alias"

instance SentenceSymbolOrAlias SentenceSymbol where
    getSentenceSymbolOrAliasConstructor =
        symbolConstructor . sentenceSymbolSymbol
    getSentenceSymbolOrAliasSortParams = symbolParams . sentenceSymbolSymbol
    getSentenceSymbolOrAliasArgumentSorts = sentenceSymbolSorts
    getSentenceSymbolOrAliasResultSort = sentenceSymbolResultSort
    getSentenceSymbolOrAliasAttributes = sentenceSymbolAttributes
    getSentenceSymbolOrAliasSentenceName _ = "symbol"

class AsSentence sentenceType s | s -> sentenceType where
    asSentence :: s -> sentenceType

data SortedPattern level variable child = SortedPattern
    { sortedPatternPattern :: !(Pattern level variable child)
    , sortedPatternSort    :: !(Sort level)
    }

{-|'PatternStub' is either a pattern with a known sort, or a function that
builds a pattern from a sort.
-}
data PatternStub level variable child
    = SortedPatternStub !(SortedPattern level variable child)
    | UnsortedPatternStub (Sort level -> Pattern level variable child)

{-|'withSort' transforms an 'UnsortedPatternStub' in a 'SortedPatternStub'.
-}
withSort
    :: Sort level
    -> PatternStub level variable child
    -> PatternStub level variable child
withSort s (UnsortedPatternStub p) =
    SortedPatternStub SortedPattern
        { sortedPatternPattern = p s
        , sortedPatternSort = s
        }
withSort
    s
    p@(SortedPatternStub SortedPattern { sortedPatternSort = existingSort })
  =
    if s == existingSort
        then p
        else
            error
                (  "Unmatched sorts: "
                ++ show s
                ++ " and "
                ++ show existingSort
                ++ "."
                )
