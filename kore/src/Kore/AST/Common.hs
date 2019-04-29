{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

This module includes all the data structures necessary for representing
the syntactic categories of a Kore definition that do not need unified
constructs.

Unified constructs are those that represent both meta and object versions of
an AST term in a single data type (e.g. 'UnifiedSort' that can be either
'Sort' or 'Sort')

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.AST.Common where

import           Control.DeepSeq
                 ( NFData (..) )
import           Data.Deriving
                 ( makeLiftCompare, makeLiftEq, makeLiftShowsPrec )
import           Data.Functor.Classes
import           Data.Functor.Const
                 ( Const )
import           Data.Functor.Identity
                 ( Identity (..) )
import           Data.Hashable
import           Data.String
                 ( fromString )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Data.Void
                 ( Void )
import           GHC.Generics
                 ( Generic )

import Kore.AST.MetaOrObject
import Kore.Sort
import Kore.Syntax.And
import Kore.Syntax.Application
import Kore.Syntax.Bottom
import Kore.Syntax.Ceil
import Kore.Syntax.CharLiteral
import Kore.Syntax.Floor
import Kore.Syntax.Or
import Kore.Syntax.SetVariable
import Kore.Syntax.StringLiteral
import Kore.Syntax.Top
import Kore.Unparser
import Template.Tools
       ( newDefinitionGroup )

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
    unparse2 = ("\\" <>) . fromString . patternString

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
    { domainValueSort  :: !Sort
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
    unparse2 = unparse

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
    { equalsOperandSort :: !Sort
    , equalsResultSort  :: !Sort
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

    unparse2
        Equals
            { equalsFirst
            , equalsSecond
            }
      = Pretty.parens (Pretty.fillSep
            [ "\\equals"
            , unparse2 equalsFirst
            , unparse2 equalsSecond
            ])

{-|'Exists' corresponds to the @\exists@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'existsSort' is both the sort of the operands and the sort of the result.

This represents the '∃existsVariable(existsChild)' Matching Logic construct.
-}
data Exists level variable child = Exists
    { existsSort     :: !Sort
    , existsVariable :: !variable
    , existsChild    :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq variable => Eq1 (Exists lvl variable) where
    liftEq = $(makeLiftEq ''Exists)

instance Ord variable => Ord1 (Exists lvl variable) where
    liftCompare = $(makeLiftCompare ''Exists)

instance Show variable => Show1 (Exists lvl variable) where
    liftShowsPrec = $(makeLiftShowsPrec ''Exists)

instance (Eq child, Eq variable) => Eq (Exists lvl variable child) where
    (==) = eq1

instance (Ord child, Ord variable) => Ord (Exists lvl variable child) where
    compare = compare1

instance (Show child, Show variable) => Show (Exists lvl variable child) where
    showsPrec = showsPrec1

instance (Hashable child, Hashable variable) => Hashable (Exists lvl variable child)

instance (NFData child, NFData variable) => NFData (Exists lvl variable child)

instance
    ( Unparse child
    , Unparse variable
    ) =>
    Unparse (Exists level variable child)
  where
    unparse Exists { existsSort, existsVariable, existsChild } =
        "\\exists"
        <> parameters [existsSort]
        <> arguments' [unparse existsVariable, unparse existsChild]

    unparse2 Exists { existsVariable, existsChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\exists"
            , unparse2BindingVariables existsVariable
            , unparse2 existsChild
            ])

{-|'Forall' corresponds to the @\forall@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'forallSort' is both the sort of the operands and the sort of the result.

This represents the '∀forallVariable(forallChild)' Matching Logic construct.
-}
data Forall level variable child = Forall
    { forallSort     :: !Sort
    , forallVariable :: !variable
    , forallChild    :: child
    }
    deriving (Functor, Foldable, Traversable, Generic)

$newDefinitionGroup

instance Eq variable => Eq1 (Forall lvl variable) where
    liftEq = $(makeLiftEq ''Forall)

instance Ord variable => Ord1 (Forall lvl variable) where
    liftCompare = $(makeLiftCompare ''Forall)

instance Show variable => Show1 (Forall lvl variable) where
    liftShowsPrec = $(makeLiftShowsPrec ''Forall)

instance (Eq child, Eq variable) => Eq (Forall lvl variable child) where
    (==) = eq1

instance (Ord child, Ord variable) => Ord (Forall lvl variable child) where
    compare = compare1

instance (Show child, Show variable) => Show (Forall lvl variable child) where
    showsPrec = showsPrec1

instance (Hashable child, Hashable variable) => Hashable (Forall lvl variable child)

instance (NFData child, NFData variable) => NFData (Forall lvl variable child)

instance
    ( Unparse child
    , Unparse variable
    ) =>
    Unparse (Forall level variable child)
  where
    unparse Forall { forallSort, forallVariable, forallChild } =
        "\\forall"
        <> parameters [forallSort]
        <> arguments' [unparse forallVariable, unparse forallChild]

    unparse2 Forall { forallVariable, forallChild } =
        Pretty.parens (Pretty.fillSep
            [ "\\forall"
            , unparse2BindingVariables forallVariable
            , unparse2 forallChild
            ])

{-|'Iff' corresponds to the @\iff@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'iffSort' is both the sort of the operands and the sort of the result.

This represents the 'iffFirst ⭤ iffSecond' Matching Logic construct.
-}
data Iff level child = Iff
    { iffSort   :: !Sort
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

    unparse2 Iff { iffFirst, iffSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\iff"
            , unparse2 iffFirst
            , unparse2 iffSecond
            ])

{-|'Implies' corresponds to the @\implies@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'impliesSort' is both the sort of the operands and the sort of the result.

This represents the 'impliesFirst ⭢ impliesSecond' Matching Logic construct.
-}
data Implies level child = Implies
    { impliesSort   :: !Sort
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

    unparse2 Implies { impliesFirst, impliesSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\implies"
            , unparse2 impliesFirst
            , unparse2 impliesSecond
            ])

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
    { inOperandSort     :: !Sort
    , inResultSort      :: !Sort
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

    unparse2
        In
            { inContainedChild
            , inContainingChild
            }
      = Pretty.parens (Pretty.fillSep
            [ "\\in"
            , unparse2 inContainedChild
            , unparse2 inContainingChild
            ])

{-|'Next' corresponds to the @\next@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

Although there is no 'meta' version of @\next@, there is a 'level' type
parameter which will always be 'Object'. The object-only restriction is
done at the 'Pattern' level.

'nextSort' is both the sort of the operand and the sort of the result.

This represents the '∘ nextChild' Matching Logic construct.
-}
data Next level child = Next
    { nextSort  :: !Sort
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

    unparse2 Next { nextChild } =
        Pretty.parens (Pretty.fillSep ["\\next", unparse2 nextChild])

{-|'Not' corresponds to the @\not@ branches of the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).

The 'level' type parameter is used to distiguish between the meta- and object-
versions of symbol declarations. It should verify 'MetaOrObject level'.

'notSort' is both the sort of the operand and the sort of the result.

This represents the '¬ notChild' Matching Logic construct.
-}
data Not level child = Not
    { notSort  :: !Sort
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

    unparse2 Not { notChild } =
        Pretty.parens (Pretty.fillSep ["\\not", unparse2 notChild])

{-|'Rewrites' corresponds to the @\rewrites@ branch of the @object-pattern@
syntactic category from the Semantics of K, Section 9.1.4 (Patterns).

Although there is no 'Meta' version of @\rewrites@, there is a 'level' type
parameter which will always be 'Object'. The object-only restriction is
done at the Pattern level.

'rewritesSort' is both the sort of the operands and the sort of the result.

This represents the 'rewritesFirst ⇒ rewritesSecond' Matching Logic construct.
-}

data Rewrites level child = Rewrites
    { rewritesSort   :: !Sort
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

    unparse2 Rewrites { rewritesFirst, rewritesSecond } =
        Pretty.parens (Pretty.fillSep
            [ "\\rewrites"
            , unparse2 rewritesFirst
            , unparse2 rewritesSecond
            ])

{-|'Pattern' corresponds to the @object-pattern@ and
@meta-pattern@ syntactic categories from the Semantics of K,
Section 9.1.4 (Patterns).
-}
-- NOTE: If you are adding a case to Pattern, you should add cases in:
-- ASTUtils/SmartConstructors.hs
-- as well as a ton of other places, probably.
data Pattern level domain variable child where
    AndPattern
        :: !(And Sort child) -> Pattern level domain variable child
    ApplicationPattern
        :: !(Application SymbolOrAlias child)
        -> Pattern level domain variable child
    BottomPattern
        :: !(Bottom Sort child) -> Pattern level domain variable child
    CeilPattern
        :: !(Ceil Sort child) -> Pattern level domain variable child
    DomainValuePattern
        :: !(domain child)
        -> Pattern level domain variable child
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
        :: !(Next level child) -> Pattern level domain variable child
    NotPattern
        :: !(Not level child) -> Pattern level domain variable child
    OrPattern
        :: !(Or Sort child) -> Pattern level domain variable child
    RewritesPattern
        :: !(Rewrites level child) -> Pattern level domain variable child
    StringLiteralPattern
        :: !StringLiteral -> Pattern level domain variable child
    CharLiteralPattern
        :: !CharLiteral -> Pattern level domain variable child
    TopPattern
        :: !(Top Sort child) -> Pattern level domain variable child
    VariablePattern
        :: !variable -> Pattern level domain variable child
    InhabitantPattern
        :: !Sort -> Pattern level domain variable child
    SetVariablePattern
        :: !(SetVariable variable) -> Pattern level domain variable child

$newDefinitionGroup
{- dummy top-level splice to make ''Pattern available for lifting -}

instance
    (Eq variable, Eq1 domain) =>
    Eq1 (Pattern level domain variable)
  where
    liftEq = $(makeLiftEq ''Pattern)

instance
    (Ord variable, Ord1 domain) =>
    Ord1 (Pattern level domain variable)
  where
    liftCompare = $(makeLiftCompare ''Pattern)

instance
    (Show variable, Show1 domain) =>
    Show1 (Pattern level domain variable)
  where
    liftShowsPrec = $(makeLiftShowsPrec ''Pattern)

deriving instance Generic (Pattern level domain variable child)

instance
    ( Hashable child
    , Hashable variable
    , Hashable (domain child)
    ) =>
    Hashable (Pattern level domain variable child)

instance
    ( NFData child
    , NFData variable
    , NFData (domain child)
    ) =>
    NFData (Pattern level domain variable child)

instance
    (Eq child, Eq variable, Eq1 domain) =>
    Eq (Pattern level domain variable child)
  where
    (==) = eq1

instance
    (Ord child, Ord variable, Ord1 domain) =>
    Ord (Pattern level domain variable child)
  where
    compare = compare1

instance
    (Show child, Show variable, Show1 domain) =>
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
    , Unparse variable
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
            InhabitantPattern s          -> unparse s
            SetVariablePattern p   -> unparse p

    unparse2 =
        \case
            AndPattern p           -> unparse2 p
            ApplicationPattern p   -> unparse2 p
            BottomPattern p        -> unparse2 p
            CeilPattern p          -> unparse2 p
            DomainValuePattern p   -> unparse2 p
            EqualsPattern p        -> unparse2 p
            ExistsPattern p        -> unparse2 p
            FloorPattern p         -> unparse2 p
            ForallPattern p        -> unparse2 p
            IffPattern p           -> unparse2 p
            ImpliesPattern p       -> unparse2 p
            InPattern p            -> unparse2 p
            NextPattern p          -> unparse2 p
            NotPattern p           -> unparse2 p
            OrPattern p            -> unparse2 p
            RewritesPattern p      -> unparse2 p
            StringLiteralPattern p -> unparse2 p
            CharLiteralPattern p   -> unparse2 p
            TopPattern p           -> unparse2 p
            VariablePattern p      -> unparse2 p
            InhabitantPattern s          -> unparse s
            SetVariablePattern p   -> unparse p

{-|'dummySort' is used in error messages when we want to convert an
'UnsortedPatternStub' to a pattern that can be displayed.
-}
dummySort :: Sort
dummySort = SortVariableSort (SortVariable (noLocationId "dummy"))

{- | Use the provided mapping to replace all variables in a 'Pattern' head.

__Warning__: @mapVariables@ will capture variables if the provided mapping is
not injective!

-}
mapVariables
    :: (variable1 -> variable2)
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
    => (variable1 -> f variable2)
    -> Pattern level domain variable1 child
    -> f (Pattern level domain variable2 child)
traverseVariables traversing =
    \case
        -- Non-trivial cases
        ExistsPattern any0 -> ExistsPattern <$> traverseVariablesExists any0
        ForallPattern all0 -> ForallPattern <$> traverseVariablesForall all0
        VariablePattern variable -> VariablePattern <$> traversing variable
        InhabitantPattern s -> pure (InhabitantPattern s)
        SetVariablePattern (SetVariable variable)
            -> SetVariablePattern . SetVariable <$> traversing variable
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
        InhabitantPattern s -> InhabitantPattern s
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
        SetVariablePattern varP -> SetVariablePattern varP

{- | Cast a 'Pattern' head with @'Const' 'Void'@ domain values into any domain.

The @Const Void@ domain excludes domain values; the pattern head can be cast
trivially because it must contain no domain values.

 -}
castVoidDomainValues
    :: Pattern level (Const Void) variable child
    -> Pattern level domain       variable child
castVoidDomainValues = mapDomainValues (\case {})
