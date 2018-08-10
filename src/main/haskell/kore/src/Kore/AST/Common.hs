{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE TemplateHaskell #-}
{-|
Module      : Kore.AST.Common
Description : Data Structures for representing the Kore language AST that do not
              need unified constructs (see "Kore.AST.Kore" for the unified
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
module Kore.AST.Common where

import Control.DeepSeq
       ( NFData (..) )
import Data.Deriving
       ( deriveEq1, deriveOrd1, deriveShow1, makeLiftCompare, makeLiftEq,
       makeLiftShowsPrec )
import Data.Functor.Classes
import Data.Functor.Foldable
       ( Fix (..) )
import Data.Hashable
import Data.Proxy
import Data.String
       ( fromString )
import GHC.Generics
       ( Generic )

import           Data.Functor.Foldable.Orphans ()
import           Kore.AST.MetaOrObject
import           Kore.AST.Pretty
                 ( Pretty (..), (<>) )
import qualified Kore.AST.Pretty as Pretty
import           Kore.Parser.CString
                 ( escapeCString )

{-| 'FileLocation' represents a position in a source file.
-}
data FileLocation = FileLocation
    { fileName :: FilePath
    , line     :: Int
    , column   :: Int
    }
    deriving (Eq, Show, Generic)

instance Hashable FileLocation
instance NFData FileLocation

{-| 'AstLocation' represents the origin of an AST node.

Its representation may change, e.g. the `AstLocationFile` branch could become a
range instead of a single character position. You should treat the entire
AstLocation as much as possible as an opaque token, i.e. hopefully only
the kore parsing code and pretty printing code below would access
the AstLocationFile branch.
-}
data AstLocation
    = AstLocationNone
    | AstLocationImplicit
    | AstLocationGeneratedVariable
    | AstLocationTest
    | AstLocationFile FileLocation
    | AstLocationLifted AstLocation
    | AstLocationUnknown
    -- ^ This should not be used and should be eliminated in further releases
    deriving (Eq, Show, Generic)

instance Hashable AstLocation
instance NFData AstLocation

{-| 'prettyPrintAstLocation' displays an `AstLocation` in a way that's
(sort of) user friendly.
-}
prettyPrintAstLocation :: AstLocation -> String
prettyPrintAstLocation AstLocationNone = "<unknown location>"
prettyPrintAstLocation AstLocationImplicit = "<implicitly defined entity>"
prettyPrintAstLocation AstLocationGeneratedVariable =
    "<variable generated internally>"
prettyPrintAstLocation AstLocationTest = "<test data>"
prettyPrintAstLocation
    (AstLocationFile FileLocation
        { fileName = name
        , line = line'
        , column = column'
        }
    )
    = name ++ " " ++ show line' ++ ":" ++ show column'
prettyPrintAstLocation (AstLocationLifted location) =
    "<lifted(" ++ prettyPrintAstLocation location ++ ")>"
prettyPrintAstLocation AstLocationUnknown = "<unknown location>"

{-|'Id' corresponds to the @object-identifier@ and @meta-identifier@
syntactic categories from the Semantics of K, Section 9.1.1 (Lexicon).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

We may chage the Id's representation in the future so one should treat it as
an opaque entity as much as possible.

Note that Id comparison ignores the AstLocation.
-}
data Id level = Id
    { getId      :: !String
    , idLocation :: !AstLocation
    }
    deriving (Show, Generic)

instance Ord (Id level) where
    compare first@(Id _ _) second@(Id _ _) =
        compare (getId first) (getId second)

{-# ANN module ("HLint: ignore Redundant compare" :: String) #-}
instance Eq (Id level) where
    first == second = compare first second == EQ

instance Hashable (Id level)

instance NFData (Id level)

instance Pretty (Id level) where
    pretty Id { getId } = fromString getId

{-| 'noLocationId' creates an Id without a source location. While there are some
narrow cases where this makes sense, you should really consider other options
(including adding a new entry to the `AstLocation` data definition).
-}
noLocationId :: String -> Id level
noLocationId value = Id
    { getId = value
    , idLocation = AstLocationNone
    }

{-|'StringLiteral' corresponds to the @string@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype StringLiteral = StringLiteral { getStringLiteral :: String }
    deriving (Show, Eq, Ord, Generic)

instance Hashable StringLiteral

instance NFData StringLiteral

instance Pretty StringLiteral where
    pretty StringLiteral {..} =
        (Pretty.dquotes . fromString . escapeCString) getStringLiteral

{-|'CharLiteral' corresponds to the @char@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype CharLiteral = CharLiteral { getCharLiteral :: Char }
    deriving (Show, Eq, Ord, Generic)

instance Hashable CharLiteral

instance NFData CharLiteral

instance Pretty CharLiteral where
    pretty CharLiteral {..} =
        (Pretty.squotes . fromString . escapeCString . (: [])) getCharLiteral

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
    deriving (Show, Eq, Ord, Generic)

instance Hashable (SymbolOrAlias level)

instance NFData (SymbolOrAlias level)

instance Pretty (SymbolOrAlias level) where
    pretty SymbolOrAlias {..} =
        pretty symbolOrAliasConstructor <> Pretty.parameters symbolOrAliasParams

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
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Symbol level)

instance NFData (Symbol level)

instance Pretty (Symbol level) where
    pretty Symbol {..} =
        pretty symbolConstructor <> Pretty.parameters symbolParams

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
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Alias level)

instance NFData (Alias level)

instance Pretty (Alias level) where
    pretty Alias {..} =
        pretty aliasConstructor <> Pretty.parameters aliasParams

{-|'SortVariable' corresponds to the @object-sort-variable@ and
@meta-sort-variable@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
newtype SortVariable level = SortVariable
    { getSortVariable  :: Id level }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (SortVariable level)

instance NFData (SortVariable level)

instance Pretty (SortVariable level) where
    pretty = pretty . getSortVariable

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
    deriving (Show, Eq, Ord, Generic)

instance Hashable (SortActual level)

instance NFData (SortActual level)

instance Pretty (SortActual level) where
    pretty SortActual {..} =
        pretty sortActualName <> Pretty.parameters sortActualSorts

{-|'Sort' corresponds to the @object-sort@ and
@meta-sort@ syntactic categories from the Semantics of K,
Section 9.1.2 (Sorts).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
data Sort level
    = SortVariableSort !(SortVariable level)
    | SortActualSort !(SortActual level)
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Sort level)

instance NFData (Sort level)

instance Pretty (Sort level) where
    pretty (SortVariableSort sortVariable) = pretty sortVariable
    pretty (SortActualSort sortActual)     = pretty sortActual

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
    | UserSort String -- arbitrary MetaSort
    deriving(Generic)

instance Hashable MetaBasicSortType

data MetaSortType
    = MetaBasicSortType MetaBasicSortType
    | MetaListSortType MetaBasicSortType
    | StringSort
    deriving(Generic)

instance Hashable MetaSortType

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
metaBasicSortTypeString CharSort        = "Char"
metaBasicSortTypeString PatternSort     = "Pattern"
metaBasicSortTypeString SortSort        = "Sort"
metaBasicSortTypeString SymbolSort      = "Symbol"
metaBasicSortTypeString VariableSort    = "Variable"
metaBasicSortTypeString (UserSort name) =  name

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
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Variable level)

instance NFData (Variable level)

instance Pretty (Variable level) where
    pretty Variable {..} =
        pretty variableName <> Pretty.colon <> pretty variableSort

{-| 'SortedVariable' is a variable which has a sort.
-}
class SortedVariable variable where
    sortedVariableSort :: variable level -> Sort level

instance SortedVariable Variable where
    sortedVariableSort = variableSort

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
    deriving (Show, Generic)

instance Hashable MLPatternType

instance Pretty MLPatternType where
  pretty = ("\\" <>) . fromString . patternString

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''And
deriveOrd1 ''And
deriveShow1 ''And

instance Hashable child => Hashable (And level child)

instance NFData child => NFData (And level child)

instance Pretty child => Pretty (And level child) where
    pretty And {..} =
        "\\and"
        <> Pretty.parameters [andSort]
        <> Pretty.arguments [andFirst, andSecond]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Application
deriveOrd1 ''Application
deriveShow1 ''Application

instance Hashable child => Hashable (Application level child)

instance NFData child => NFData (Application level child)

instance Pretty child => Pretty (Application level child) where
    pretty Application {..} =
        pretty applicationSymbolOrAlias <> Pretty.arguments applicationChildren

{-|'Bottom' corresponds to the @\bottom@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'bottomSort' is the sort of the result.

This represents the ⌈BottomPattern⌉ Matching Logic construct.
-}
newtype Bottom level child = Bottom { bottomSort :: Sort level}
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Bottom
deriveOrd1 ''Bottom
deriveShow1 ''Bottom

instance Hashable (Bottom level child)

instance NFData (Bottom level child)

instance Pretty child => Pretty (Bottom level child) where
    pretty Bottom {..} =
        "\\bottom" <> Pretty.parameters [bottomSort] <> Pretty.noArguments

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Ceil
deriveOrd1 ''Ceil
deriveShow1 ''Ceil

instance Hashable child => Hashable (Ceil level child)

instance NFData child => NFData (Ceil level child)

instance Pretty child => Pretty (Ceil level child) where
    pretty Ceil {..} =
        "\\ceil"
        <> Pretty.parameters [ceilOperandSort, ceilResultSort]
        <> Pretty.arguments [ceilChild]

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
    deriving (Eq, Ord, Show, Generic)

deriveEq1 ''DomainValue
deriveOrd1 ''DomainValue
deriveShow1 ''DomainValue

instance Hashable child => Hashable (DomainValue level child)

instance NFData child => NFData (DomainValue level child)

instance Pretty child => Pretty (DomainValue level child) where
    pretty DomainValue {..} =
        "\\dv"
        <> Pretty.parameters [domainValueSort]
        <> Pretty.arguments [domainValueChild]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Equals
deriveOrd1 ''Equals
deriveShow1 ''Equals

instance Hashable child => Hashable (Equals level child)

instance NFData child => NFData (Equals level child)

instance Pretty child => Pretty (Equals level child) where
    pretty Equals {..} =
        "\\equals"
        <> Pretty.parameters [equalsOperandSort, equalsResultSort]
        <> Pretty.arguments [equalsFirst, equalsSecond]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance (Ord (Sort level), Ord (v level)) => Ord1 (Exists level v) where
    liftCompare liftedCompare a b =
        (existsSort a `compare` existsSort b)
        <> (existsVariable a `compare` existsVariable b)
        <> (existsChild a) `liftedCompare` (existsChild b)

instance (Eq (Sort level), Eq (v level)) => Eq1 (Exists level v) where
    liftEq liftedEq a b =
        (existsSort a == existsSort b)
        && (existsVariable a == existsVariable b)
        && liftedEq (existsChild a) (existsChild b)

instance (Show (Sort level), Show (v level)) => Show1 (Exists level v) where
    liftShowsPrec liftedShowsPrec _ _ e =
        showString "Exists { "
        . showString "existsSort = " . shows (existsSort e)
        . showString ", existsVariable = " . shows (existsVariable e)
        . showString ", existsChild = " . liftedShowsPrec 0 (existsChild e)
        . showString " }"

instance (Hashable child, Hashable (v level)) => Hashable (Exists level v child)

instance (NFData child, NFData (var level)) => NFData (Exists level var child)

instance (Pretty child, Pretty (variable level)) =>
    Pretty (Exists level variable child) where
    pretty Exists {..} =
        "\\exists"
        <> Pretty.parameters [existsSort]
        <> Pretty.arguments' [pretty existsVariable, pretty existsChild]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Floor
deriveOrd1 ''Floor
deriveShow1 ''Floor

instance Hashable child => Hashable (Floor level child)

instance NFData child => NFData (Floor level child)

instance Pretty child => Pretty (Floor level child) where
    pretty Floor {..} =
        "\\floor"
        <> Pretty.parameters [floorOperandSort, floorResultSort]
        <> Pretty.arguments [floorChild]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

instance (Ord (Sort level), Ord (v level)) => Ord1 (Forall level v) where
    liftCompare liftedCompare a b =
        (forallSort a `compare` forallSort b)
        <> (forallVariable a `compare` forallVariable b)
        <> (forallChild a) `liftedCompare` (forallChild b)

instance (Eq (Sort level), Eq (v level)) => Eq1 (Forall level v) where
    liftEq liftedEq a b =
        (forallSort a == forallSort b)
        && (forallVariable a == forallVariable b)
        && liftedEq (forallChild a) (forallChild b)

instance (Show (Sort level), Show (v level)) => Show1 (Forall level v) where
    liftShowsPrec liftedShowsPrec _ _ e =
        showString "Forall { "
        . showString "forallSort = " . shows (forallSort e)
        . showString ", forallVariable = " . shows (forallVariable e)
        . showString ", forallChild = " . liftedShowsPrec 0 (forallChild e)
        . showString " }"

instance (Hashable child, Hashable (v level)) => Hashable (Forall level v child)

instance (NFData child, NFData (v level)) => NFData (Forall level v child)

instance (Pretty child, Pretty (variable level)) =>
    Pretty (Forall level variable child) where
    pretty Forall {..} =
        "\\forall"
        <> Pretty.parameters [forallSort]
        <> Pretty.arguments' [pretty forallVariable, pretty forallChild]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Iff
deriveOrd1 ''Iff
deriveShow1 ''Iff

instance Hashable child => Hashable (Iff level child)

instance NFData child => NFData (Iff level child)

instance Pretty child => Pretty (Iff level child) where
    pretty Iff {..} =
        "\\iff"
        <> Pretty.parameters [iffSort]
        <> Pretty.arguments [iffFirst, iffSecond]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Implies
deriveOrd1 ''Implies
deriveShow1 ''Implies

instance Hashable child => Hashable (Implies level child)

instance NFData child => NFData (Implies level child)

instance Pretty child => Pretty (Implies level child) where
    pretty Implies {..} =
        "\\implies"
        <> Pretty.parameters [impliesSort]
        <> Pretty.arguments [impliesFirst, impliesSecond]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''In
deriveOrd1 ''In
deriveShow1 ''In

instance Hashable child => Hashable (In level child)

instance NFData child => NFData (In level child)

instance Pretty child => Pretty (In level child) where
    pretty In {..} =
        "\\in"
        <> Pretty.parameters [inOperandSort, inResultSort]
        <> Pretty.arguments [inContainedChild, inContainingChild]


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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Next
deriveOrd1 ''Next
deriveShow1 ''Next

instance Hashable child => Hashable (Next level child)

instance NFData child => NFData (Next level child)

instance Pretty child => Pretty (Next level child) where
    pretty Next {..} =
        "\\next"
        <> Pretty.parameters [nextSort]
        <> Pretty.arguments [nextChild]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Not
deriveOrd1 ''Not
deriveShow1 ''Not

instance Hashable child => Hashable (Not level child)

instance NFData child => NFData (Not level child)

instance Pretty child => Pretty (Not level child) where
    pretty Not {..} =
        "\\not"
        <> Pretty.parameters [notSort]
        <> Pretty.arguments [notChild]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Or
deriveOrd1 ''Or
deriveShow1 ''Or

instance Hashable child => Hashable (Or level child)

instance NFData child => NFData (Or level child)

instance Pretty child => Pretty (Or level child) where
    pretty Or {..} =
        "\\or"
        <> Pretty.parameters [orSort]
        <> Pretty.arguments [orFirst, orSecond]

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
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Rewrites
deriveOrd1 ''Rewrites
deriveShow1 ''Rewrites

instance Hashable child => Hashable (Rewrites level child)

instance NFData child => NFData (Rewrites level child)

instance Pretty child => Pretty (Rewrites level child) where
    pretty Rewrites {..} =
        "\\rewrites"
        <> Pretty.parameters [rewritesSort]
        <> Pretty.arguments [rewritesFirst, rewritesSecond]

{-|'Top' corresponds to the @\top@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'topSort' is the sort of the result.

This represents the ⌈TopPattern⌉ Matching Logic construct.
-}
newtype Top level child = Top { topSort :: Sort level}
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)

deriveEq1 ''Top
deriveOrd1 ''Top
deriveShow1 ''Top

instance Hashable (Top level child)

instance NFData (Top level child)

instance Pretty child => Pretty (Top level child) where
    pretty Top {..} =
        "\\top" <> Pretty.parameters [topSort] <> Pretty.noArguments

{-|'Pattern' corresponds to the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

Note that the 'StringLiteralPattern' and 'CharLiteralPattern' should
be members only of 'Pattern Meta'.
-}
-- NOTE: If you are adding a case to Pattern, you should add cases in:
-- ASTUtils/SmartConstructors.hs
-- as well as a ton of other places, probably.
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
        :: !(DomainValue Object (Fix (Pattern Meta Variable))) -> Pattern Object variable child
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

$(return [])
{- dummy top-level splice to make ''Pattern available for lifting -}

instance (Ord level, Ord (variable level)) => Ord1 (Pattern level variable) where
    liftCompare liftedCompare a b = $(makeLiftCompare ''Pattern) liftedCompare a b

instance (Eq level, Eq (variable level)) => Eq1 (Pattern level variable) where
    liftEq liftedEq a b = $(makeLiftEq ''Pattern) liftedEq a b

instance (Show level, Show (variable level)) => Show1 (Pattern level variable) where
    liftShowsPrec = $(makeLiftShowsPrec ''Pattern)

-- instance Generic child => Generic (Pattern level variable child)

-- instance (Hashable child, Generic child, Hashable (variable level))
-- => Hashable (Pattern level variable child)

instance (Hashable child, Hashable (variable level))
 => Hashable (Pattern level variable child) where
  hashWithSalt s = \case
    AndPattern           p -> s `hashWithSalt` (0::Int) `hashWithSalt` p
    ApplicationPattern   p -> s `hashWithSalt` (1::Int) `hashWithSalt` p
    BottomPattern        p -> s `hashWithSalt` (2::Int) `hashWithSalt` p
    CeilPattern          p -> s `hashWithSalt` (3::Int) `hashWithSalt` p
    DomainValuePattern   p -> s `hashWithSalt` (4::Int) `hashWithSalt` p
    EqualsPattern        p -> s `hashWithSalt` (5::Int) `hashWithSalt` p
    ExistsPattern        p -> s `hashWithSalt` (6::Int) `hashWithSalt` p
    FloorPattern         p -> s `hashWithSalt` (7::Int) `hashWithSalt` p
    ForallPattern        p -> s `hashWithSalt` (8::Int) `hashWithSalt` p
    IffPattern           p -> s `hashWithSalt` (9::Int) `hashWithSalt` p
    ImpliesPattern       p -> s `hashWithSalt` (10::Int) `hashWithSalt` p
    InPattern            p -> s `hashWithSalt` (11::Int) `hashWithSalt` p
    NextPattern          p -> s `hashWithSalt` (12::Int) `hashWithSalt` p
    NotPattern           p -> s `hashWithSalt` (13::Int) `hashWithSalt` p
    OrPattern            p -> s `hashWithSalt` (14::Int) `hashWithSalt` p
    RewritesPattern      p -> s `hashWithSalt` (15::Int) `hashWithSalt` p
    StringLiteralPattern p -> s `hashWithSalt` (16::Int) `hashWithSalt` p
    CharLiteralPattern   p -> s `hashWithSalt` (17::Int) `hashWithSalt` p
    TopPattern           p -> s `hashWithSalt` (18::Int) `hashWithSalt` p
    VariablePattern      p -> s `hashWithSalt` (19::Int) `hashWithSalt` p

instance (NFData child, NFData (var level)) => NFData (Pattern level var child) where
    rnf =
        \case
            AndPattern p -> rnf p
            ApplicationPattern p -> rnf p
            BottomPattern p -> rnf p
            CeilPattern p -> rnf p
            DomainValuePattern p -> rnf p
            EqualsPattern p -> rnf p
            ExistsPattern p -> rnf p
            FloorPattern p -> rnf p
            ForallPattern p -> rnf p
            IffPattern p -> rnf p
            ImpliesPattern p -> rnf p
            InPattern p -> rnf p
            NextPattern p -> rnf p
            NotPattern p -> rnf p
            OrPattern p -> rnf p
            RewritesPattern p -> rnf p
            StringLiteralPattern p -> rnf p
            CharLiteralPattern p -> rnf p
            TopPattern p -> rnf p
            VariablePattern p -> rnf p

deriving instance
    ( Eq child
    , Eq (variable level)
    ) => Eq (Pattern level variable child)
deriving instance
    ( Show child
    , Show (variable level)
    ) => Show (Pattern level variable child)
deriving instance
    ( Ord child
    , Ord (variable level)
    ) => Ord (Pattern level variable child)
deriving instance Functor (Pattern level variable)
deriving instance Foldable (Pattern level variable)
deriving instance Traversable (Pattern level variable)

instance (Pretty child, Pretty (variable level)) =>
    Pretty (Pattern level variable child) where
    pretty (AndPattern p)           = pretty p
    pretty (ApplicationPattern p)   = pretty p
    pretty (BottomPattern p)        = pretty p
    pretty (CeilPattern p)          = pretty p
    pretty (DomainValuePattern p)   = pretty p
    pretty (EqualsPattern p)        = pretty p
    pretty (ExistsPattern p)        = pretty p
    pretty (FloorPattern p)         = pretty p
    pretty (ForallPattern p)        = pretty p
    pretty (IffPattern p)           = pretty p
    pretty (ImpliesPattern p)       = pretty p
    pretty (InPattern p)            = pretty p
    pretty (NextPattern p)          = pretty p
    pretty (NotPattern p)           = pretty p
    pretty (OrPattern p)            = pretty p
    pretty (RewritesPattern p)      = pretty p
    pretty (StringLiteralPattern p) = pretty p
    pretty (CharLiteralPattern p)   = pretty p
    pretty (TopPattern p)           = pretty p
    pretty (VariablePattern p)      = pretty p

data SortedPattern level variable child = SortedPattern
    { sortedPatternPattern :: !(Pattern level variable child)
    , sortedPatternSort    :: !(Sort level)
    }
    deriving (Eq, Show, Generic)

instance (Hashable child, Hashable (variable level))
  => Hashable (SortedPattern level variable child)

{-|'PatternStub' is either a pattern with a known sort, or a function that
builds a pattern from a sort.
-}
data PatternStub level variable child
    = SortedPatternStub !(SortedPattern level variable child)
    | UnsortedPatternStub (Sort level -> Pattern level variable child)
    deriving(Generic)

-- cannot hash.

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

{-|'dummySort' is used in error messages when we want to convert an
'UnsortedPatternStub' to a pattern that can be displayed.
-}
dummySort :: MetaOrObject level => proxy level -> Sort level
dummySort proxy =
    SortVariableSort
        (SortVariable
            (noLocationId
                (case isMetaOrObject proxy of
                    IsMeta   -> "#dummy"
                    IsObject -> "dummy"
                )
            )
        )

{-|'getMetaOrObjectPatternType' is a helper function useful to determine
whether a 'Pattern' is 'Object' or 'Meta'.
-}
getMetaOrObjectPatternType
    :: MetaOrObject level
    => Pattern level variable child -> IsMetaOrObject level
getMetaOrObjectPatternType _ = isMetaOrObject (Proxy :: Proxy level)

{-|The 'UnifiedPatternInterface' class provides a common interface for
algorithms providing common functionality for 'KorePattern' and 'PurePattern'.
-}
class UnifiedPatternInterface pat where
    -- |View a 'Meta' 'Pattern' as the parameter @pat@ of the class.
    unifyMetaPattern :: Pattern Meta variable child -> pat variable child
    unifyMetaPattern = unifyPattern
    -- |View an 'Object' 'Pattern' as the parameter @pat@ of the class.
    unifyObjectPattern :: Pattern Object variable child -> pat variable child
    unifyObjectPattern = unifyPattern
    -- |View a 'Meta' or an 'Object' 'Pattern' as the parameter of the class.
    unifyPattern
        :: MetaOrObject level
        => Pattern level variable child -> pat variable child
    unifyPattern p =
        case getMetaOrObjectPatternType p of
            IsMeta   -> unifyMetaPattern p
            IsObject -> unifyObjectPattern p
    -- |Given a function appliable on all 'Meta' or 'Object' 'Pattern's,
    -- apply it on an object of the parameter @pat@ of the class.
    unifiedPatternApply
        :: (forall level . MetaOrObject level
            => Pattern level variable child -> result
           )
        -> (pat variable child -> result)

instance
    forall level . MetaOrObject level
    => UnifiedPatternInterface (Pattern level)
  where
    unifyMetaPattern p =
        case isMetaOrObject (Proxy :: Proxy level) of
            IsMeta   -> p
            IsObject -> error "Expecting Meta pattern"
    unifyObjectPattern p =
        case isMetaOrObject (Proxy :: Proxy level) of
            IsObject -> p
            IsMeta   -> error "Expecting Object pattern"
    unifiedPatternApply = id
