{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE KindSignatures    #-}
module Data.Kore.AST.CommonBase where

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
data And level child = And
    { andSort   :: !(Sort level)
    , andFirst  :: !child
    , andSecond :: !child
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Application' corresponds to the @head(pattern-list)@ branches of the
@object-pattern@ and @meta-pattern@ syntactic categories from
the Semantics of K, Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

This represents the σ(φ1, ..., φn) symbol patterns in Matching Logic.
-}
data Application level child = Application
    { applicationSymbolOrAlias :: !(SymbolOrAlias level)
    , applicationChildren      :: ![child]
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
newtype Bottom level child = Bottom { bottomSort :: Sort level}
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
data Ceil level child = Ceil
    { ceilOperandSort :: !(Sort level)
    , ceilResultSort  :: !(Sort level)
    , ceilChild       :: !child
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
data DomainValue level child = DomainValue
    { domainValueSort  :: !(Sort level)
    , domainValueChild :: !child
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
data Equals level child = Equals
    { equalsOperandSort :: !(Sort level)
    , equalsResultSort  :: !(Sort level)
    , equalsFirst       :: !child
    , equalsSecond      :: !child
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
data Exists level v child = Exists
    { existsSort     :: !(Sort level)
    , existsVariable :: !(v level)
    , existsChild    :: !child
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
data Floor level child = Floor
    { floorOperandSort :: !(Sort level)
    , floorResultSort  :: !(Sort level)
    , floorChild       :: !child
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
data Forall level v child = Forall
    { forallSort     :: !(Sort level)
    , forallVariable :: !(v level)
    , forallChild    :: !child
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
data Iff level child = Iff
    { iffSort   :: !(Sort level)
    , iffFirst  :: !child
    , iffSecond :: !child
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
data Implies level child = Implies
    { impliesSort   :: !(Sort level)
    , impliesFirst  :: !child
    , impliesSecond :: !child
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
data In level child = In
    { inOperandSort     :: !(Sort level)
    , inResultSort      :: !(Sort level)
    , inContainedChild  :: !child
    , inContainingChild :: !child
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
data Next level child = Next
    { nextSort  :: !(Sort level)
    , nextChild :: !child
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
data Not level child = Not
    { notSort  :: !(Sort level)
    , notChild :: !child
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
data Or level child = Or
    { orSort   :: !(Sort level)
    , orFirst  :: !child
    , orSecond :: !child
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

data Rewrites level child = Rewrites
    { rewritesSort   :: !(Sort level)
    , rewritesFirst  :: !child
    , rewritesSecond :: !child
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
newtype Top level child = Top { topSort :: Sort level}
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)


{-|'Attributes' corresponds to the @attributes@ Kore syntactic declaration.
It is parameterized by the types of Patterns, @pat@.
-}
newtype Attributes pat (variable :: * -> *) =
    Attributes { getAttributes :: [pat variable] }
  deriving (Eq, Show)
