{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE StandaloneDeriving     #-}
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

import           Data.Hashable (hash)
import           Data.Typeable (Typeable, cast, typeOf, typeRepArgs)

data KoreLevel
    = ObjectLevel
    | MetaLevel
    deriving (Eq, Show)

class (Ord a, Show a, Typeable a) => IsMeta a where
    koreLevel :: a -> KoreLevel

data Meta = Meta
    deriving (Show, Eq, Ord, Typeable)

instance IsMeta Meta where
    koreLevel _ = MetaLevel

data Object = Object
    deriving (Show, Eq, Ord, Typeable)

instance IsMeta Object where
    koreLevel _ = ObjectLevel

isObject :: (IsMeta a, Typeable (m a)) => m a -> Bool
isObject x = head (typeRepArgs (typeOf x)) == typeOf Object

isMeta :: (IsMeta a, Typeable (m a)) => m a -> Bool
isMeta x = head (typeRepArgs (typeOf x)) == typeOf Meta

applyMetaObjectFunction
    :: (IsMeta a, Typeable thing)
    => thing a -> (thing Object -> c) -> (thing Meta -> c) -> c
applyMetaObjectFunction x = applyMetaObjectFunctionCasted (cast x) (cast x)
applyMetaObjectFunctionCasted
    :: Maybe (thing Object)
    -> Maybe (thing Meta)
    -> (thing Object -> c)
    -> (thing Meta -> c)
    -> c
applyMetaObjectFunctionCasted (Just x) Nothing f _ = f x
applyMetaObjectFunctionCasted Nothing (Just x) _ f = f x
applyMetaObjectFunctionCasted _ _ _ _ =
    error "applyMetaObjectFunctionCasted: this should not happen!"

class Typeable thing
    => UnifiedThing unifiedThing thing | unifiedThing -> thing
  where
    destructor :: unifiedThing -> Either (thing Meta) (thing Object)
    objectConstructor :: thing Object -> unifiedThing
    metaConstructor :: thing Meta -> unifiedThing
    transformUnified
        :: (forall a . IsMeta a => thing a -> b)
        -> (unifiedThing -> b)
    transformUnified f unifiedStuff =
        case destructor unifiedStuff of
            Left x  -> f x
            Right x -> f x
    asUnified :: (IsMeta a) => thing a -> unifiedThing
    asUnified x = applyMetaObjectFunction x objectConstructor metaConstructor

{-|'Id' corresponds to the @object-identifier@ and @meta-identifier@
syntactic categories from the Semantics of K, Section 9.1.1 (Lexicon).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

We may chage the Id's representation in the future so one should treat it as
an opaque entity as much as possible.
-}
newtype Id a = Id { getId :: String }
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

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
data SymbolOrAlias a = SymbolOrAlias
    { symbolOrAliasConstructor :: !(Id a)
    , symbolOrAliasParams      :: ![Sort a]
    }
    deriving (Show, Eq, Ord, Typeable)

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
    deriving (Show, Eq, Ord, Typeable)

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
    deriving (Show, Eq, Ord, Typeable)

{-|'SortVariable' corresponds to the @object-sort-variable@ and
@meta-sort-variable@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
newtype SortVariable a = SortVariable
    { getSortVariable  :: Id a }
    deriving (Show, Eq, Ord, Typeable)

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
    deriving (Show, Eq, Ord, Typeable)

{-|'Sort' corresponds to the @object-sort@ and
@meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
data Sort a
    = SortVariableSort !(SortVariable a)
    | SortActualSort !(SortActual a)
    deriving (Show, Eq, Ord, Typeable)

data UnifiedSort
    = ObjectSort !(Sort Object)
    | MetaSort !(Sort Meta)
    deriving (Show, Eq)

instance UnifiedThing UnifiedSort Sort where
    destructor (MetaSort s)   = Left s
    destructor (ObjectSort s) = Right s
    metaConstructor = MetaSort
    objectConstructor = ObjectSort

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
    , SortListSort, SymbolSort, SymbolListSort
    , VariableSort, VariableListSort
    ]
metaSortsListWithString :: [MetaSortType]
metaSortsListWithString = StringSort : metaSortsList

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
    deriving (Show, Eq, Ord)

instance UnifiedThing UnifiedSortVariable SortVariable where
    destructor (MetaSortVariable v)   = Left v
    destructor (ObjectSortVariable v) = Right v
    metaConstructor = MetaSortVariable
    objectConstructor = ObjectSortVariable

{-|'ModuleName' corresponds to the @module-name@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
newtype ModuleName = ModuleName { getModuleName :: String }
    deriving (Show, Eq, Ord)

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
    deriving (Show, Eq, Ord, Typeable)

class ( Ord (UnifiedVariable var)
      , Show (var Object), Show (var Meta)
      , Typeable var
      ) => VariableClass var
  where
    -- |Retrieves the sort of the variable
    getVariableSort :: IsMeta a => var a -> Sort a
    -- |Computes a hash identifying the variable
    getVariableHash :: var a -> Int

instance VariableClass Variable where
    getVariableSort = variableSort
    getVariableHash = hash . getId . variableName

{-|'UnifiedVariable' corresponds to the @variable@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
data UnifiedVariable v
    = MetaVariable !(v Meta)
    | ObjectVariable !(v Object)

instance Typeable v => UnifiedThing (UnifiedVariable v) v where
    destructor (MetaVariable v)   = Left v
    destructor (ObjectVariable v) = Right v
    metaConstructor = MetaVariable
    objectConstructor = ObjectVariable

deriving instance Eq (UnifiedVariable Variable)
deriving instance Ord (UnifiedVariable Variable)
deriving instance Show (UnifiedVariable Variable)

{-|'FixPattern' class corresponds to "fixed point"-like representations
of the 'Pattern' class.

'p' is the fiexd point wrapping pattern.

'v' is the type of variables.
-}
class UnifiedThing (p v) (PatternObjectMeta v (p v))
    => FixPattern v p
  where
    {-|'fixPatternApply' "lifts" a function defined on 'Pattern' to the
    domain of the fixed point 'p'.

    The resulting function unwraps the pattern from 'p' and maps it through
    the argument function.
    -}
    fixPatternApply
        :: (forall a . IsMeta a => Pattern a v (p v) -> b)
        -> (p v -> b)
    fixPatternApply f = transformUnified (f . getPatternObjectMeta)

data FixedPattern variable
    = MetaPattern !(Pattern Meta variable (FixedPattern variable))
    | ObjectPattern !(Pattern Object variable (FixedPattern variable))

{-|'UnifiedPattern' corresponds to the @pattern@ syntactic category from
the Semantics of K, Section 9.1.4 (Patterns).
-}
type UnifiedPattern = FixedPattern Variable

deriving instance Eq UnifiedPattern
deriving instance Show UnifiedPattern

instance Typeable v
    => UnifiedThing (FixedPattern v) (PatternObjectMeta v (FixedPattern v))
  where
    destructor (MetaPattern p)   = Left (PatternObjectMeta p)
    destructor (ObjectPattern p) = Right (PatternObjectMeta p)
    metaConstructor = MetaPattern . getPatternObjectMeta
    objectConstructor = ObjectPattern . getPatternObjectMeta

asUnifiedPattern
    :: (IsMeta a, Typeable v)
    => Pattern a v (FixedPattern v) -> FixedPattern v
asUnifiedPattern = asUnified . PatternObjectMeta


instance (Typeable var) => FixPattern var FixedPattern where

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

allPatternTypes :: [MLPatternType]
allPatternTypes =
    [ AndPatternType
    , BottomPatternType
    , CeilPatternType
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
    AndPatternType      -> "and"
    BottomPatternType   -> "bottom"
    CeilPatternType     -> "ceil"
    EqualsPatternType   -> "equals"
    ExistsPatternType   -> "exists"
    FloorPatternType    -> "floor"
    ForallPatternType   -> "forall"
    IffPatternType      -> "iff"
    ImpliesPatternType  -> "implies"
    InPatternType       -> "in"
    NextPatternType     -> "next"
    NotPatternType      -> "not"
    OrPatternType       -> "or"
    RewritesPatternType -> "rewrites"
    TopPatternType      -> "top"

{-|'And' corresponds to the @\and@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'andSort' is both the sort of the operands and the sort of the result.

This represents the 'andFirst ∧ andSecond' Matching Logic construct.
-}
data And a p = And
    { andSort   :: !(Sort a)
    , andFirst  :: !p
    , andSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Application' corresponds to the @head(pattern-list)@ branches of the
@object-pattern@ and @meta-pattern@ syntactic categories from
the Semantics of K, Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

This represents the σ(φ1, ..., φn) symbol patterns in Matching Logic.
-}
data Application a p = Application
    { applicationSymbolOrAlias :: !(SymbolOrAlias a)
    , applicationChildren      :: ![p]
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Bottom' corresponds to the @\bottom@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'bottomSort' is the sort of the result.

This represents the ⌈BottomPattern⌉ Matching Logic construct.
-}
newtype Bottom a p = Bottom { bottomSort :: Sort a}
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Ceil' corresponds to the @\ceil@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'ceilOperandSort' is the sort of the operand.

'ceilResultSort' is the sort of the result.

This represents the ⌈ceilPattern⌉ Matching Logic construct.
-}
data Ceil a p = Ceil
    { ceilOperandSort :: !(Sort a)
    , ceilResultSort  :: !(Sort a)
    , ceilChild       :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Equals' corresponds to the @\equals@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'equalsOperandSort' is the sort of the operand.

'equalsResultSort' is the sort of the result.

This represents the 'equalsFirst = equalsSecond' Matching Logic construct.
-}
data Equals a p = Equals
    { equalsOperandSort :: !(Sort a)
    , equalsResultSort  :: !(Sort a)
    , equalsFirst       :: !p
    , equalsSecond      :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Exists' corresponds to the @\exists@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'existsSort' is both the sort of the operands and the sort of the result.

This represents the '∃existsVariable(existsChild)' Matching Logic construct.
-}
data Exists a v p = Exists
    { existsSort     :: !(Sort a)
    , existsVariable :: !(v a)
    , existsChild    :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Floor' corresponds to the @\floor@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'floorOperandSort' is the sort of the operand.

'floorResultSort' is the sort of the result.

This represents the '⌊floorPattern⌋' Matching Logic construct.
-}
data Floor a p = Floor
    { floorOperandSort :: !(Sort a)
    , floorResultSort  :: !(Sort a)
    , floorChild       :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'forallSort' is both the sort of the operands and the sort of the result.

This represents the '∀forallVariable(forallChild)' Matching Logic construct.
-}
data Forall a v p = Forall
    { forallSort     :: !(Sort a)
    , forallVariable :: !(v a)
    , forallChild    :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Iff' corresponds to the @\iff@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'iffSort' is both the sort of the operands and the sort of the result.

This represents the 'iffFirst ⭤ iffSecond' Matching Logic construct.
-}
data Iff a p = Iff
    { iffSort   :: !(Sort a)
    , iffFirst  :: !p
    , iffSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Implies' corresponds to the @\implies@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'impliesSort' is both the sort of the operands and the sort of the result.

This represents the 'impliesFirst ⭢ impliesSecond' Matching Logic construct.
-}
data Implies a p = Implies
    { impliesSort   :: !(Sort a)
    , impliesFirst  :: !p
    , impliesSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'In' corresponds to the @\in@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'inOperandSort' is the sort of the operands.

'inResultSort' is the sort of the result.

This represents the 'inContainedChild ∊ inContainingChild' Matching Logic
construct, which, when 'inContainedChild' is a singleton (e.g. a variable),
represents the set membership. However, in general, it actually means that the
two patterns have a non-empty intersection.
-}
data In a p = In
    { inOperandSort     :: !(Sort a)
    , inResultSort      :: !(Sort a)
    , inContainedChild  :: !p
    , inContainingChild :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)


{-|'Next' corresponds to the @\next@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

Although there is no 'meta' version of @\next@, there is an 'a' type parameter
which should verify 'IsMeta a'. The object-only restriction is done at the
Pattern level.

'nextSort' is both the sort of the operand and the sort of the result.

This represents the '∘ nextChild' Matching Logic construct.
-}
data Next a p = Next
    { nextSort  :: !(Sort a)
    , nextChild :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Not' corresponds to the @\not@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'notSort' is both the sort of the operand and the sort of the result.

This represents the '¬ notChild' Matching Logic construct.
-}
data Not a p = Not
    { notSort  :: !(Sort a)
    , notChild :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Or' corresponds to the @\or@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'orSort' is both the sort of the operands and the sort of the result.

This represents the 'orFirst ∨ orSecond' Matching Logic construct.
-}
data Or a p = Or
    { orSort   :: !(Sort a)
    , orFirst  :: !p
    , orSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Rewrites' corresponds to the @\rewrites@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

Although there is no 'meta' version of @\rewrites@, there is an 'a' type
parameter which should verify 'IsMeta a'. The object-only restriction is
done at the Pattern level.

'rewritesSort' is both the sort of the operands and the sort of the result.

This represents the 'rewritesFirst ⇒ rewritesSecond' Matching Logic construct.
-}

data Rewrites a p = Rewrites
    { rewritesSort   :: !(Sort a)
    , rewritesFirst  :: !p
    , rewritesSecond :: !p
    }
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Top' corresponds to the @\top@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

'topSort' is the sort of the result.

This represents the ⌈TopPattern⌉ Matching Logic construct.
-}
newtype Top a p = Top { topSort :: Sort a}
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

{-|'Pattern' corresponds to the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.

Note that the 'StringLiteralPattern' and 'CharLiteralPattern' should
be members only of 'Pattern Meta'.
-}
data Pattern a v p
    = AndPattern !(And a p)
    | ApplicationPattern !(Application a p)
    | BottomPattern !(Bottom a p)
    | CeilPattern !(Ceil a p)
    | EqualsPattern !(Equals a p)
    | ExistsPattern !(Exists a v p)
    | FloorPattern !(Floor a p)
    | ForallPattern !(Forall a v p)
    | IffPattern !(Iff a p)
    | ImpliesPattern !(Implies a p)
    | InPattern !(In a p)
    | NextPattern !(Next Object p)
    | NotPattern !(Not a p)
    | OrPattern !(Or a p)
    | RewritesPattern !(Rewrites Object p)
    | StringLiteralPattern !StringLiteral
    | CharLiteralPattern !CharLiteral
    | TopPattern !(Top a p)
    | VariablePattern !(v a)
    deriving (Eq, Show, Typeable, Functor, Foldable, Traversable)

newtype PatternObjectMeta v p a = PatternObjectMeta
    { getPatternObjectMeta :: Pattern a v p }

{-|'SentenceAlias' corresponds to the @object-alias-declaration@ and
@meta-alias-declaration@ syntactic categories from the Semantics of K,
Section 9.1.6 (Declaration and Definitions).

The 'a' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'IsMeta a'.
-}
data SentenceAlias a = SentenceAlias
    { sentenceAliasAlias      :: !(Alias a)
    , sentenceAliasSorts      :: ![Sort a]
    , sentenceAliasResultSort :: !(Sort a)
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
    , sentenceSymbolResultSort :: !(Sort a)
    , sentenceSymbolAttributes :: !Attributes
    }
    deriving (Eq, Show, Typeable)


{-|'SentenceImport' corresponds to the @import-declaration@ syntactic category
from the Semantics of K, Section 9.1.6 (Declaration and Definitions).
-}
data SentenceImport = SentenceImport
    { sentenceImportModuleName :: !ModuleName
    , sentenceImportAttributes :: !Attributes
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
    | SentenceImportSentence !SentenceImport
    | SentenceAxiomSentence !SentenceAxiom
    | SentenceSortSentence !SentenceSort
    deriving (Eq, Show)

asSentenceAliasSentence :: IsMeta a => SentenceAlias a -> Sentence
asSentenceAliasSentence v =
    applyMetaObjectFunction
        v ObjectSentenceAliasSentence MetaSentenceAliasSentence


asSentenceSymbolSentence :: IsMeta a => SentenceSymbol a -> Sentence
asSentenceSymbolSentence v =
    applyMetaObjectFunction
        v ObjectSentenceSymbolSentence MetaSentenceSymbolSentence


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
    , definitionModules    :: ![Module]
    }
    deriving (Eq, Show)

class AsSentence s where
    asSentence :: s -> Sentence

instance AsSentence (SentenceAlias Meta) where
    asSentence = MetaSentenceAliasSentence

instance AsSentence (SentenceAlias Object) where
    asSentence = ObjectSentenceAliasSentence

instance AsSentence (SentenceSymbol Meta) where
    asSentence = MetaSentenceSymbolSentence

instance AsSentence (SentenceSymbol Object) where
    asSentence = ObjectSentenceSymbolSentence

instance AsSentence SentenceImport where
    asSentence = SentenceImportSentence

instance AsSentence SentenceAxiom where
    asSentence = SentenceAxiomSentence

instance AsSentence SentenceSort where
    asSentence = SentenceSortSentence


{-|'MLPatternClass' offers a common interface to ML patterns
  (those starting with '\', except for 'Exists' and 'Forall')
-}
class MLPatternClass p where
    getPatternType :: p a recursionP -> MLPatternType
    getMLPatternOperandSorts :: p a recursionP -> [Sort a]
    getMLPatternResultSort :: p a recursionP -> Sort a
    getPatternSorts :: p a recursionP -> [Sort a]
    getPatternChildren :: p a recursionP -> [recursionP]

instance MLPatternClass And where
    getPatternType _ = AndPatternType
    getMLPatternOperandSorts x = [andSort x, andSort x]
    getMLPatternResultSort = andSort
    getPatternSorts a = [andSort a]
    getPatternChildren a = [andFirst a, andSecond a]

instance MLPatternClass Bottom where
    getPatternType _ = BottomPatternType
    getMLPatternOperandSorts _ = []
    getMLPatternResultSort = bottomSort
    getPatternSorts t = [bottomSort t]
    getPatternChildren _ = []

instance MLPatternClass Ceil where
    getPatternType _ = CeilPatternType
    getMLPatternOperandSorts x = [ceilOperandSort x]
    getMLPatternResultSort = ceilResultSort
    getPatternSorts c = [ceilOperandSort c, ceilResultSort c]
    getPatternChildren c = [ceilChild c]

instance MLPatternClass Equals where
    getPatternType _ = EqualsPatternType
    getMLPatternOperandSorts x = [equalsOperandSort x, equalsOperandSort x]
    getMLPatternResultSort = equalsResultSort
    getPatternSorts e = [equalsOperandSort e, equalsResultSort e]
    getPatternChildren e = [equalsFirst e, equalsSecond e]

instance MLPatternClass Floor where
    getPatternType _ = FloorPatternType
    getMLPatternOperandSorts x = [floorOperandSort x]
    getMLPatternResultSort = floorResultSort
    getPatternSorts f = [floorOperandSort f, floorResultSort f]
    getPatternChildren f = [floorChild f]

instance MLPatternClass Iff where
    getPatternType _ = IffPatternType
    getMLPatternOperandSorts x = [iffSort x, iffSort x]
    getMLPatternResultSort = iffSort
    getPatternSorts i = [iffSort i]
    getPatternChildren i = [iffFirst i, iffSecond i]

instance MLPatternClass Implies where
    getPatternType _ = ImpliesPatternType
    getMLPatternOperandSorts x = [impliesSort x, impliesSort x]
    getMLPatternResultSort = impliesSort
    getPatternSorts i = [impliesSort i]
    getPatternChildren i = [impliesFirst i, impliesSecond i]

instance MLPatternClass In where
    getPatternType _ = InPatternType
    getMLPatternOperandSorts x = [inOperandSort x, inOperandSort x]
    getMLPatternResultSort = inResultSort
    getPatternSorts i = [inOperandSort i, inResultSort i]
    getPatternChildren i = [inContainedChild i, inContainingChild i]

instance MLPatternClass Next where
    getPatternType _ = NextPatternType
    getMLPatternOperandSorts x = [nextSort x]
    getMLPatternResultSort = nextSort
    getPatternSorts e = [nextSort e]
    getPatternChildren e = [nextChild e]

instance MLPatternClass Not where
    getPatternType _ = NotPatternType
    getMLPatternOperandSorts x = [notSort x]
    getMLPatternResultSort = notSort
    getPatternSorts n = [notSort n]
    getPatternChildren n = [notChild n]

instance MLPatternClass Or where
    getPatternType _ = OrPatternType
    getMLPatternOperandSorts x = [orSort x, orSort x]
    getMLPatternResultSort = orSort
    getPatternSorts a = [orSort a]
    getPatternChildren a = [orFirst a, orSecond a]

instance MLPatternClass Rewrites where
    getPatternType _ = RewritesPatternType
    getMLPatternOperandSorts x = [rewritesSort x, rewritesSort x]
    getMLPatternResultSort = rewritesSort
    getPatternSorts e = [rewritesSort e]
    getPatternChildren e = [rewritesFirst e, rewritesSecond e]

instance MLPatternClass Top where
    getPatternType _ = TopPatternType
    getMLPatternOperandSorts _ = []
    getMLPatternResultSort = topSort
    getPatternSorts t = [topSort t]
    getPatternChildren _ = []

class MLBinderPatternClass p where
    getBinderPatternType :: p a v recursionP -> MLPatternType
    getBinderPatternSort :: p a v recursionP -> Sort a
    getBinderPatternVariable :: p a v recursionP -> v a
    getBinderPatternChild :: p a v recursionP -> recursionP
    -- The first argument is only needed in order to make the Haskell type
    -- system work.
    binderPatternConstructor
        :: p a v recursionP -> Sort a -> v a -> recursionP
        -> Pattern a v recursionP

instance MLBinderPatternClass Exists where
    getBinderPatternType _ = ExistsPatternType
    getBinderPatternSort = existsSort
    getBinderPatternVariable = existsVariable
    getBinderPatternChild = existsChild
    binderPatternConstructor _ s v p = ExistsPattern Exists
        { existsSort = s
        , existsVariable = v
        , existsChild = p
        }

instance MLBinderPatternClass Forall where
    getBinderPatternType _ = ForallPatternType
    getBinderPatternSort = forallSort
    getBinderPatternVariable = forallVariable
    getBinderPatternChild = forallChild
    binderPatternConstructor _ s v p = ForallPattern Forall
        { forallSort = s
        , forallVariable = v
        , forallChild = p
        }

class SentenceSymbolOrAlias p where
    getSentenceSymbolOrAliasConstructor :: p a -> Id a
    getSentenceSymbolOrAliasSortParams :: p a -> [SortVariable a]
    getSentenceSymbolOrAliasArgumentSorts :: p a -> [Sort a]
    getSentenceSymbolOrAliasResultSort :: p a -> Sort a
    getSentenceSymbolOrAliasAttributes :: p a -> Attributes
    getSentenceSymbolOrAliasSentenceName :: p a -> String

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
