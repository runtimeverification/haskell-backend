{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE TemplateHaskell   #-}

{-|
Module      : Kore.AST.Common
Description : Data Structures for representing the Kore language AST that do not
              need unified constructs (see "Kore.AST.Kore" for the unified
              ones).
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
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

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Deriving
                 ( makeLiftCompare, makeLiftEq, makeLiftShowsPrec )
import           Data.Function
                 ( on )
import           Data.Functor.Classes
import           Data.Functor.Const
                 ( Const )
import           Data.Functor.Identity
                 ( Identity (..) )
import           Data.Hashable
import           Data.Maybe
                 ( isNothing )
import           Data.Proxy
import           Data.String
                 ( fromString )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Generic )
import           Numeric.Natural

import Data.Sup
import Kore.AST.Identifier
import Kore.AST.MetaOrObject
import Kore.Sort
import Kore.Unparser
import Template.Tools
       ( newDefinitionGroup )

{-|'StringLiteral' corresponds to the @string@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype StringLiteral = StringLiteral { getStringLiteral :: Text }
    deriving (Show, Eq, Ord, Generic)

instance Hashable StringLiteral

instance NFData StringLiteral

instance Unparse StringLiteral where
    unparse = Pretty.dquotes . Pretty.pretty . escapeStringT . getStringLiteral

{-|'CharLiteral' corresponds to the @char@ literal from the Semantics of K,
Section 9.1.1 (Lexicon).
-}
newtype CharLiteral = CharLiteral { getCharLiteral :: Char }
    deriving (Show, Eq, Ord, Generic)

instance Hashable CharLiteral

instance NFData CharLiteral

instance Unparse CharLiteral where
    unparse = Pretty.squotes . fromString . escapeChar . getCharLiteral

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

instance Unparse (SymbolOrAlias level) where
    unparse
        SymbolOrAlias
            { symbolOrAliasConstructor
            , symbolOrAliasParams
            }
      =
        unparse symbolOrAliasConstructor <> parameters symbolOrAliasParams

{-|'Variable' corresponds to the @object-variable@ and
@meta-variable@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

Particularly, this is the type of variable in patterns returned by the parser.

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.
-}
-- Invariant [variableCounter = Just Sup]:
-- No function returns a value that would match the pattern:
--
-- > Variable { variableCounter = Just Sup }
--
-- This value of variableCounter may only be used in refreshVariable to pivot
-- the set of variables that must not be captured.
data Variable level = Variable
    { variableName :: !(Id level)
    , variableCounter :: !(Maybe (Sup Natural))
    , variableSort :: !(Sort level)
    }
    deriving (Show, Eq, Ord, Generic)

instance Hashable (Variable level)

instance NFData (Variable level)

instance Unparse (Variable level) where
    unparse Variable { variableName, variableSort } =
        unparse variableName <> Pretty.colon <> unparse variableSort

{- | Is the variable original (as opposed to generated)?
 -}
isOriginalVariable :: Variable level -> Bool
isOriginalVariable Variable { variableCounter } = isNothing variableCounter

{- | Error thrown when 'variableCounter' takes an illegal value.
 -}
illegalVariableCounter :: a
illegalVariableCounter =
    error "Illegal use of Variable { variableCounter = Just Sup }"

{- | Reset 'variableCounter' so that a 'Variable' may be unparsed.

@externalizeFreshVariable@ is not injective and is unsafe if used with
'mapVariables'. See 'Kore.Step.Pattern.externalizeFreshVariables' instead.

 -}
externalizeFreshVariable :: Variable level -> Variable level
externalizeFreshVariable variable@Variable { variableName, variableCounter } =
    variable
        { variableName = variableName'
        , variableCounter = Nothing
        }
  where
    variableName' =
        variableName
            { getId =
                case variableCounter of
                    Nothing -> getId variableName
                    Just (Element n) -> getId variableName <> Text.pack (show n)
                    Just Sup -> illegalVariableCounter
            , idLocation = AstLocationGeneratedVariable
            }

{- | @Concrete level@ is a variable occuring in a concrete pattern.

    Concrete patterns do not contain variables, so this is an uninhabited type
    (it has no constructors).

    See also: 'Data.Void.Void'

 -}
data Concrete level
    deriving (Eq, Generic, Ord, Read, Show)

instance Hashable (Concrete level)

instance NFData (Concrete level)

instance Unparse (Concrete level) where
    unparse = \case {}

{- | 'SortedVariable' is a Kore variable with a known sort.

The instances of @SortedVariable@ must encompass the 'Variable' type by
implementing 'fromVariable', i.e. we must be able to construct a
@SortedVariable@ given a parsed 'Variable'.

'toVariable' may delete information so that

> toVariable . fromVariable === id :: Variable level -> Variable level

but the reverse is not required.

 -}
class SortedVariable (variable :: * -> *) where
    -- | The known 'Sort' of the given variable.
    sortedVariableSort :: variable level -> Sort level
    sortedVariableSort variable =
        variableSort
      where
        Variable { variableSort } = toVariable variable

    -- | Convert a variable from the parsed syntax of Kore.
    fromVariable :: Variable level -> variable level
    -- | Extract the parsed syntax of a Kore variable.
    toVariable :: variable level -> Variable level

instance SortedVariable Variable where
    sortedVariableSort = variableSort
    fromVariable = id
    toVariable = id

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

instance Unparse MLPatternType where
    unparse = ("\\" <>) . fromString . patternString

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
    , andFirst  :: child
    , andSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (And level) where
    liftEq = $(makeLiftEq ''And)

instance Ord1 (And level) where
    liftCompare = $(makeLiftCompare ''And)

instance Show1 (And level) where
    liftShowsPrec = $(makeLiftShowsPrec ''And)

instance Eq child => Eq (And level child) where
    (==) = eq1

instance Ord child => Ord (And level child) where
    compare = compare1

instance Show child => Show (And level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (And level child)

instance NFData child => NFData (And level child)

instance Unparse child => Unparse (And level child) where
    unparse
        And { andSort, andFirst, andSecond }
      =
        "\\and"
        <> parameters [andSort]
        <> arguments [andFirst, andSecond]

{-|'Application' corresponds to the @head(pattern-list)@ branches of the
@object-pattern@ and @meta-pattern@ syntactic categories from
the Semantics of K, Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

This represents the σ(φ1, ..., φn) symbol patterns in Matching Logic.
-}
data Application level child = Application
    { applicationSymbolOrAlias :: !(SymbolOrAlias level)
    , applicationChildren      :: [child]
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Application level) where
    liftEq = $(makeLiftEq ''Application)

instance Ord1 (Application level) where
    liftCompare = $(makeLiftCompare ''Application)

instance Show1 (Application level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Application)

instance Eq child => Eq (Application level child) where
    (==) = eq1

instance Ord child => Ord (Application level child) where
    compare = compare1

instance Show child => Show (Application level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Application level child)

instance NFData child => NFData (Application level child)

instance Unparse child => Unparse (Application level child) where
    unparse
        Application { applicationSymbolOrAlias, applicationChildren }
      =
        unparse applicationSymbolOrAlias
        <> arguments applicationChildren

{-|'Bottom' corresponds to the @\bottom@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'bottomSort' is the sort of the result.

This represents the ⌈BottomPattern⌉ Matching Logic construct.
-}
newtype Bottom level child = Bottom { bottomSort :: Sort level }
    deriving (Functor, Foldable, Show, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Bottom level) where
    liftEq = $(makeLiftEq ''Bottom)

instance Ord1 (Bottom level) where
    liftCompare = $(makeLiftCompare ''Bottom)

instance Show1 (Bottom level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Bottom)

instance Eq (Bottom level child) where
    (==) = on (==) bottomSort

instance Ord (Bottom level child) where
    compare = on compare bottomSort

instance Hashable (Bottom level child)

instance NFData (Bottom level child)

instance Unparse (Bottom level child) where
    unparse Bottom { bottomSort } =
        "\\bottom" <> parameters [bottomSort] <> noArguments

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
    , ceilChild       :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Ceil level) where
    liftEq = $(makeLiftEq ''Ceil)

instance Ord1 (Ceil level) where
    liftCompare = $(makeLiftCompare ''Ceil)

instance Show1 (Ceil level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Ceil)

instance Eq child => Eq (Ceil level child) where
    (==) = eq1

instance Ord child => Ord (Ceil level child) where
    compare = compare1

instance Show child => Show (Ceil level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Ceil level child)

instance NFData child => NFData (Ceil level child)

instance Unparse child => Unparse (Ceil level child) where
    unparse Ceil { ceilOperandSort, ceilResultSort, ceilChild } =
        "\\ceil"
        <> parameters [ceilOperandSort, ceilResultSort]
        <> arguments [ceilChild]

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
data DomainValue level domain child = DomainValue
    { domainValueSort  :: !(Sort level)
    , domainValueChild :: !(domain child)
    }
    deriving (Foldable, Functor, Generic, Traversable)

$newDefinitionGroup

instance Eq1 domain => Eq1 (DomainValue level domain) where
    liftEq = $(makeLiftEq ''DomainValue)

instance Ord1 domain => Ord1 (DomainValue level domain) where
    liftCompare = $(makeLiftCompare ''DomainValue)

instance Show1 domain => Show1 (DomainValue level domain) where
    liftShowsPrec = $(makeLiftShowsPrec ''DomainValue)

instance (Eq1 domain, Eq child) => Eq (DomainValue level domain child) where
    (==) = eq1

instance (Ord1 domain, Ord child) => Ord (DomainValue level domain child) where
    compare = compare1

instance (Show1 dom, Show child) => Show (DomainValue lvl dom child) where
    showsPrec = showsPrec1

instance Hashable (domain child) => Hashable (DomainValue level domain child)

instance NFData (domain child) => NFData (DomainValue level domain child)

instance
    (Unparse (domain child), level ~ Object) =>
    Unparse (DomainValue level domain child)
  where
    unparse DomainValue { domainValueChild } = unparse domainValueChild

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
    , equalsFirst       :: child
    , equalsSecond      :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Equals level) where
    liftEq = $(makeLiftEq ''Equals)

instance Ord1 (Equals level) where
    liftCompare = $(makeLiftCompare ''Equals)

instance Show1 (Equals level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Equals)

instance Eq child => Eq (Equals level child) where
    (==) = eq1

instance Ord child => Ord (Equals level child) where
    compare = compare1

instance Show child => Show (Equals level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Equals level child)

instance NFData child => NFData (Equals level child)

instance Unparse child => Unparse (Equals level child) where
    unparse
        Equals
            { equalsOperandSort
            , equalsResultSort
            , equalsFirst
            , equalsSecond
            }
      =
        "\\equals"
        <> parameters [equalsOperandSort, equalsResultSort]
        <> arguments [equalsFirst, equalsSecond]

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
    , existsChild    :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq (var lvl) => Eq1 (Exists lvl var) where
    liftEq = $(makeLiftEq ''Exists)

instance Ord (var lvl) => Ord1 (Exists lvl var) where
    liftCompare = $(makeLiftCompare ''Exists)

instance Show (var lvl) => Show1 (Exists lvl var) where
    liftShowsPrec = $(makeLiftShowsPrec ''Exists)

instance (Eq child, Eq (var lvl)) => Eq (Exists lvl var child) where
    (==) = eq1

instance (Ord child, Ord (var lvl)) => Ord (Exists lvl var child) where
    compare = compare1

instance (Show child, Show (var lvl)) => Show (Exists lvl var child) where
    showsPrec = showsPrec1

instance (Hashable child, Hashable (var lvl)) => Hashable (Exists lvl var child)

instance (NFData child, NFData (var lvl)) => NFData (Exists lvl var child)

instance
    ( Unparse child
    , Unparse (variable level)
    ) =>
    Unparse (Exists level variable child)
  where
    unparse Exists { existsSort, existsVariable, existsChild } =
        "\\exists"
        <> parameters [existsSort]
        <> arguments' [unparse existsVariable, unparse existsChild]

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
    , floorChild       :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Floor level) where
    liftEq = $(makeLiftEq ''Floor)

instance Ord1 (Floor level) where
    liftCompare = $(makeLiftCompare ''Floor)

instance Show1 (Floor level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Floor)

instance Eq child => Eq (Floor level child) where
    (==) = eq1

instance Ord child => Ord (Floor level child) where
    compare = compare1

instance Show child => Show (Floor level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Floor level child)

instance NFData child => NFData (Floor level child)

instance Unparse child => Unparse (Floor level child) where
    unparse Floor { floorOperandSort, floorResultSort, floorChild } =
        "\\floor"
        <> parameters [floorOperandSort, floorResultSort]
        <> arguments [floorChild]

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
    , forallChild    :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq (var lvl) => Eq1 (Forall lvl var) where
    liftEq = $(makeLiftEq ''Forall)

instance Ord (var lvl) => Ord1 (Forall lvl var) where
    liftCompare = $(makeLiftCompare ''Forall)

instance Show (var lvl) => Show1 (Forall lvl var) where
    liftShowsPrec = $(makeLiftShowsPrec ''Forall)

instance (Eq child, Eq (var lvl)) => Eq (Forall lvl var child) where
    (==) = eq1

instance (Ord child, Ord (var lvl)) => Ord (Forall lvl var child) where
    compare = compare1

instance (Show child, Show (var lvl)) => Show (Forall lvl var child) where
    showsPrec = showsPrec1

instance (Hashable child, Hashable (var lvl)) => Hashable (Forall lvl var child)

instance (NFData child, NFData (var lvl)) => NFData (Forall lvl var child)

instance
    ( Unparse child
    , Unparse (variable level)
    ) =>
    Unparse (Forall level variable child)
  where
    unparse Forall { forallSort, forallVariable, forallChild } =
        "\\forall"
        <> parameters [forallSort]
        <> arguments' [unparse forallVariable, unparse forallChild]

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
    , iffFirst  :: child
    , iffSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Iff level) where
    liftEq = $(makeLiftEq ''Iff)

instance Ord1 (Iff level) where
    liftCompare = $(makeLiftCompare ''Iff)

instance Show1 (Iff level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Iff)

instance Eq child => Eq (Iff level child) where
    (==) = eq1

instance Ord child => Ord (Iff level child) where
    compare = compare1

instance Show child => Show (Iff level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Iff level child)

instance NFData child => NFData (Iff level child)

instance Unparse child => Unparse (Iff level child) where
    unparse Iff { iffSort, iffFirst, iffSecond } =
        "\\iff"
        <> parameters [iffSort]
        <> arguments [iffFirst, iffSecond]

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
    , impliesFirst  :: child
    , impliesSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Implies level) where
    liftEq = $(makeLiftEq ''Implies)

instance Ord1 (Implies level) where
    liftCompare = $(makeLiftCompare ''Implies)

instance Show1 (Implies level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Implies)

instance Eq child => Eq (Implies level child) where
    (==) = eq1

instance Ord child => Ord (Implies level child) where
    compare = compare1

instance Show child => Show (Implies level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Implies level child)

instance NFData child => NFData (Implies level child)

instance Unparse child => Unparse (Implies level child) where
    unparse Implies { impliesSort, impliesFirst, impliesSecond } =
        "\\implies"
        <> parameters [impliesSort]
        <> arguments [impliesFirst, impliesSecond]

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
    , inContainedChild  :: child
    , inContainingChild :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (In level) where
    liftEq = $(makeLiftEq ''In)

instance Ord1 (In level) where
    liftCompare = $(makeLiftCompare ''In)

instance Show1 (In level) where
    liftShowsPrec = $(makeLiftShowsPrec ''In)

instance Eq child => Eq (In level child) where
    (==) = eq1

instance Ord child => Ord (In level child) where
    compare = compare1

instance Show child => Show (In level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (In level child)

instance NFData child => NFData (In level child)

instance Unparse child => Unparse (In level child) where
    unparse
        In
            { inOperandSort
            , inResultSort
            , inContainedChild
            , inContainingChild
            }
      =
        "\\in"
        <> parameters [inOperandSort, inResultSort]
        <> arguments [inContainedChild, inContainingChild]

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
    , nextChild :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Next level) where
    liftEq = $(makeLiftEq ''Next)

instance Ord1 (Next level) where
    liftCompare = $(makeLiftCompare ''Next)

instance Show1 (Next level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Next)

instance Eq child => Eq (Next level child) where
    (==) = eq1

instance Ord child => Ord (Next level child) where
    compare = compare1

instance Show child => Show (Next level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Next level child)

instance NFData child => NFData (Next level child)

instance Unparse child => Unparse (Next level child) where
    unparse Next { nextSort, nextChild } =
        "\\next"
        <> parameters [nextSort]
        <> arguments [nextChild]

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
    , notChild :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Not level) where
    liftEq = $(makeLiftEq ''Not)

instance Ord1 (Not level) where
    liftCompare = $(makeLiftCompare ''Not)

instance Show1 (Not level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Not)

instance Eq child => Eq (Not level child) where
    (==) = eq1

instance Ord child => Ord (Not level child) where
    compare = compare1

instance Show child => Show (Not level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Not level child)

instance NFData child => NFData (Not level child)

instance Unparse child => Unparse (Not level child) where
    unparse Not { notSort, notChild } =
        "\\not"
        <> parameters [notSort]
        <> arguments [notChild]

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
    , orFirst  :: child
    , orSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Or level) where
    liftEq = $(makeLiftEq ''Or)

instance Ord1 (Or level) where
    liftCompare = $(makeLiftCompare ''Or)

instance Show1 (Or level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Or)

instance Eq child => Eq (Or level child) where
    (==) = eq1

instance Ord child => Ord (Or level child) where
    compare = compare1

instance Show child => Show (Or level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Or level child)

instance NFData child => NFData (Or level child)

instance Unparse child => Unparse (Or level child) where
    unparse Or { orSort, orFirst, orSecond } =
        "\\or"
        <> parameters [orSort]
        <> arguments [orFirst, orSecond]

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
    , rewritesFirst  :: child
    , rewritesSecond :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Rewrites level) where
    liftEq = $(makeLiftEq ''Rewrites)

instance Ord1 (Rewrites level) where
    liftCompare = $(makeLiftCompare ''Rewrites)

instance Show1 (Rewrites level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Rewrites)

instance Eq child => Eq (Rewrites level child) where
    (==) = eq1

instance Ord child => Ord (Rewrites level child) where
    compare = compare1

instance Show child => Show (Rewrites level child) where
    showsPrec = showsPrec1

instance Hashable child => Hashable (Rewrites level child)

instance NFData child => NFData (Rewrites level child)

instance Unparse child => Unparse (Rewrites level child) where
    unparse Rewrites { rewritesSort, rewritesFirst, rewritesSecond } =
        "\\rewrites"
        <> parameters [rewritesSort]
        <> arguments [rewritesFirst, rewritesSecond]

{-|'Top' corresponds to the @\top@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'topSort' is the sort of the result.

This represents the ⌈TopPattern⌉ Matching Logic construct.
-}
newtype Top level child = Top { topSort :: Sort level}
    deriving (Functor, Foldable, Show, Traversable, Generic)

$newDefinitionGroup

instance Eq1 (Top level) where
    liftEq = $(makeLiftEq ''Top)

instance Ord1 (Top level) where
    liftCompare = $(makeLiftCompare ''Top)

instance Show1 (Top level) where
    liftShowsPrec = $(makeLiftShowsPrec ''Top)

instance Eq (Top level child) where
    (==) = on (==) topSort

instance Ord (Top level child) where
    compare = on compare topSort

instance Hashable (Top level child)

instance NFData (Top level child)

instance Unparse (Top level child) where
    unparse Top { topSort } =
        "\\top" <> parameters [topSort] <> noArguments

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
data Pattern level domain variable child where
    AndPattern
        :: !(And level child) -> Pattern level domain variable child
    ApplicationPattern
        :: !(Application level child) -> Pattern level domain variable child
    BottomPattern
        :: !(Bottom level child) -> Pattern level domain variable child
    CeilPattern
        :: !(Ceil level child) -> Pattern level domain variable child
    DomainValuePattern
        :: !(domain child)
        -> Pattern Object domain variable child
    EqualsPattern
        :: !(Equals level child) -> Pattern level domain variable child
    ExistsPattern
        :: !(Exists level variable child) -> Pattern level domain variable child
    FloorPattern
        :: !(Floor level child) -> Pattern level domain variable child
    ForallPattern
        :: !(Forall level variable child) -> Pattern level domain variable child
    IffPattern
        :: !(Iff level child) -> Pattern level domain variable child
    ImpliesPattern
        :: !(Implies level child) -> Pattern level domain variable child
    InPattern
        :: !(In level child) -> Pattern level domain variable child
    NextPattern
        :: !(Next Object child) -> Pattern Object domain variable child
    NotPattern
        :: !(Not level child) -> Pattern level domain variable child
    OrPattern
        :: !(Or level child) -> Pattern level domain variable child
    RewritesPattern
        :: !(Rewrites Object child) -> Pattern Object domain variable child
    StringLiteralPattern
        :: !StringLiteral -> Pattern Meta domain variable child
    CharLiteralPattern
        :: !CharLiteral -> Pattern Meta domain variable child
    TopPattern
        :: !(Top level child) -> Pattern level domain variable child
    VariablePattern
        :: !(variable level) -> Pattern level domain variable child

$newDefinitionGroup
{- dummy top-level splice to make ''Pattern available for lifting -}

instance
    (Eq (variable level), Eq1 domain) =>
    Eq1 (Pattern level domain variable)
  where
    liftEq = $(makeLiftEq ''Pattern)

instance
    (Ord (variable level), Ord1 domain) =>
    Ord1 (Pattern level domain variable)
  where
    liftCompare = $(makeLiftCompare ''Pattern)

instance
    (Show (variable level), Show1 domain) =>
    Show1 (Pattern level domain variable)
  where
    liftShowsPrec = $(makeLiftShowsPrec ''Pattern)

instance
    ( Hashable child
    , Hashable (variable level)
    , Hashable (domain child)
    ) =>
    Hashable (Pattern level domain variable child)
  where
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

instance
    ( NFData child
    , NFData (var level)
    , NFData (domain child)
    ) =>
    NFData (Pattern level domain var child)
  where
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

instance
    (Eq child, Eq (variable level), Eq1 domain) =>
    Eq (Pattern level domain variable child)
  where
    (==) = eq1

instance
    (Ord child, Ord (variable level), Ord1 domain) =>
    Ord (Pattern level domain variable child)
  where
    compare = compare1

instance
    (Show child, Show (variable level), Show1 domain) =>
    Show (Pattern level domain variable child)
  where
    showsPrec = showsPrec1

deriving instance Functor domain => Functor (Pattern level domain variable)

deriving instance Foldable domain => Foldable (Pattern level domain variable)

deriving instance
    Traversable domain => Traversable (Pattern level domain variable)

instance
    ( Unparse child
    , Unparse (domain child)
    , Unparse (variable level)
    ) =>
    Unparse (Pattern level domain variable child)
  where
    unparse =
        \case
            AndPattern p           -> unparse p
            ApplicationPattern p   -> unparse p
            BottomPattern p        -> unparse p
            CeilPattern p          -> unparse p
            DomainValuePattern p   -> unparse p
            EqualsPattern p        -> unparse p
            ExistsPattern p        -> unparse p
            FloorPattern p         -> unparse p
            ForallPattern p        -> unparse p
            IffPattern p           -> unparse p
            ImpliesPattern p       -> unparse p
            InPattern p            -> unparse p
            NextPattern p          -> unparse p
            NotPattern p           -> unparse p
            OrPattern p            -> unparse p
            RewritesPattern p      -> unparse p
            StringLiteralPattern p -> unparse p
            CharLiteralPattern p   -> unparse p
            TopPattern p           -> unparse p
            VariablePattern p      -> unparse p

data SortedPattern level domain variable child = SortedPattern
    { sortedPatternPattern :: !(Pattern level domain variable child)
    , sortedPatternSort    :: !(Sort level)
    }
    deriving (Eq, Show, Generic)

instance (NFData child, NFData (variable level), NFData (domain child))
    => NFData (SortedPattern level domain variable child)

instance
    ( Hashable child
    , Hashable (variable level)
    , Hashable (domain child)
    ) =>
    Hashable (SortedPattern level domain variable child)

{-|'PatternStub' is either a pattern with a known sort, or a function that
builds a pattern from a sort.
-}
data PatternStub level domain variable child
    = SortedPatternStub !(SortedPattern level domain variable child)
    | UnsortedPatternStub (Sort level -> Pattern level domain variable child)
    deriving(Generic)

instance (NFData child, NFData (variable level), NFData (domain child))
    => NFData (PatternStub level domain variable child)

-- cannot hash.

{-|'withSort' transforms an 'UnsortedPatternStub' in a 'SortedPatternStub'.
-}
withSort
    :: Sort level
    -> PatternStub level domain variable child
    -> PatternStub level domain variable child
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
    => Pattern level domain variable child -> IsMetaOrObject level
getMetaOrObjectPatternType _ = isMetaOrObject (Proxy :: Proxy level)

{-|The 'UnifiedPatternInterface' class provides a common interface for
algorithms providing common functionality for 'KorePattern' and 'PurePattern'.
-}
class UnifiedPatternInterface pat where
    -- |View a 'Meta' 'Pattern' as the parameter @pat@ of the class.
    unifyMetaPattern
        :: Pattern Meta domain variable child
        -> pat domain variable child
    unifyMetaPattern = unifyPattern

    -- |View an 'Object' 'Pattern' as the parameter @pat@ of the class.
    unifyObjectPattern
        :: Pattern Object domain variable child
        -> pat domain variable child
    unifyObjectPattern = unifyPattern

    -- |View a 'Meta' or an 'Object' 'Pattern' as the parameter of the class.
    unifyPattern
        :: MetaOrObject level
        => Pattern level domain variable child
        -> pat domain variable child
    unifyPattern p =
        case getMetaOrObjectPatternType p of
            IsMeta   -> unifyMetaPattern p
            IsObject -> unifyObjectPattern p

    -- |Given a function appliable on all 'Meta' or 'Object' 'Pattern's,
    -- apply it on an object of the parameter @pat@ of the class.
    unifiedPatternApply
        ::  (forall level . MetaOrObject level =>
                Pattern level domain variable child -> result
            )
        -> (pat domain variable child -> result)

instance
    forall level . MetaOrObject level =>
    UnifiedPatternInterface (Pattern level)
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

{- | Use the provided mapping to replace all variables in a 'Pattern' head.

__Warning__: @mapVariables@ will capture variables if the provided mapping is
not injective!

-}
mapVariables
    :: (variable1 level -> variable2 level)
    -> Pattern level domain variable1 child
    -> Pattern level domain variable2 child
mapVariables mapping =
    runIdentity . traverseVariables (Identity . mapping)
{-# INLINE mapVariables #-}

{- | Use the provided traversal to replace all variables in a 'Pattern' head.

__Warning__: @traverseVariables@ will capture variables if the provided
traversal is not injective!

-}
traverseVariables
    :: Applicative f
    => (variable1 level -> f (variable2 level))
    -> Pattern level domain variable1 child
    -> f (Pattern level domain variable2 child)
traverseVariables traversing =
    \case
        -- Non-trivial cases
        ExistsPattern any0 -> ExistsPattern <$> traverseVariablesExists any0
        ForallPattern all0 -> ForallPattern <$> traverseVariablesForall all0
        VariablePattern variable -> VariablePattern <$> traversing variable
        -- Trivial cases
        AndPattern andP -> pure (AndPattern andP)
        ApplicationPattern appP -> pure (ApplicationPattern appP)
        BottomPattern botP -> pure (BottomPattern botP)
        CeilPattern ceilP -> pure (CeilPattern ceilP)
        DomainValuePattern dvP -> pure (DomainValuePattern dvP)
        EqualsPattern eqP -> pure (EqualsPattern eqP)
        FloorPattern flrP -> pure (FloorPattern flrP)
        IffPattern iffP -> pure (IffPattern iffP)
        ImpliesPattern impP -> pure (ImpliesPattern impP)
        InPattern inP -> pure (InPattern inP)
        NextPattern nxtP -> pure (NextPattern nxtP)
        NotPattern notP -> pure (NotPattern notP)
        OrPattern orP -> pure (OrPattern orP)
        RewritesPattern rewP -> pure (RewritesPattern rewP)
        StringLiteralPattern strP -> pure (StringLiteralPattern strP)
        CharLiteralPattern charP -> pure (CharLiteralPattern charP)
        TopPattern topP -> pure (TopPattern topP)
  where
    traverseVariablesExists Exists { existsSort, existsVariable, existsChild } =
        Exists existsSort <$> traversing existsVariable <*> pure existsChild
    traverseVariablesForall Forall { forallSort, forallVariable, forallChild } =
        Forall forallSort <$> traversing forallVariable <*> pure forallChild

-- | Use the provided mapping to replace all domain values in a 'Pattern' head.
mapDomainValues
    :: (forall child'. domain1 child' -> domain2 child')
    -> Pattern level domain1 variable child
    -> Pattern level domain2 variable child
mapDomainValues mapping =
    \case
        -- Non-trivial case
        DomainValuePattern domainP -> DomainValuePattern (mapping domainP)
        -- Trivial cases
        AndPattern andP -> AndPattern andP
        ApplicationPattern appP -> ApplicationPattern appP
        BottomPattern botP -> BottomPattern botP
        CeilPattern ceilP -> CeilPattern ceilP
        EqualsPattern eqP -> EqualsPattern eqP
        ExistsPattern existsP -> ExistsPattern existsP
        FloorPattern flrP -> FloorPattern flrP
        ForallPattern forallP -> ForallPattern forallP
        IffPattern iffP -> IffPattern iffP
        ImpliesPattern impP -> ImpliesPattern impP
        InPattern inP -> InPattern inP
        NextPattern nextP -> NextPattern nextP
        NotPattern notP -> NotPattern notP
        OrPattern orP -> OrPattern orP
        RewritesPattern rewP -> RewritesPattern rewP
        StringLiteralPattern strP -> StringLiteralPattern strP
        CharLiteralPattern charP -> CharLiteralPattern charP
        TopPattern topP -> TopPattern topP
        VariablePattern varP -> VariablePattern varP

{- | Cast a 'Pattern' head with @'Const' 'Void'@ domain values into any domain.

The @Const Void@ domain excludes domain values; the pattern head can be cast
trivially because it must contain no domain values.

 -}
castVoidDomainValues
    :: Pattern level (Const Void) variable child
    -> Pattern level domain       variable child
castVoidDomainValues = mapDomainValues (\case {})
