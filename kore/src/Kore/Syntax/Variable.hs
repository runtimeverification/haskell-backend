{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Please refer to Section 9 (The Kore Language) of the
<http://github.com/kframework/kore/blob/master/docs/semantics-of-k.pdf Semantics of K>.
-}

{-# LANGUAGE EmptyDataDeriving #-}

module Kore.Syntax.Variable
    ( Variable (..)
    , isOriginalVariable
    , illegalVariableCounter
    , externalizeFreshVariable
    , Variable1 (..)
    , SomeVariable1
    , ElementVariable1
    , SetVariable1
    -- * Variable names
    , VariableName (..)
    , ElementVariableName (..)
    , SetVariableName (..)
    , SomeVariableName (..)
    , AdjSomeVariableName (..)
    , mapSomeVariableName
    , mapElementVariableName
    , mapSetVariableName
    , traverseSomeVariableName
    , traverseElementVariableName
    , traverseSetVariableName
    , NamedVariable (..)
    , lensVariableName
    , fromVariable1
    , toVariable1
    , VariableBase
    , toVariable
    , fromVariable
    , toVariableName
    , fromVariableName
    -- * Variable sorts
    , SortedVariable (..)
    , sortedVariableSort
    , unparse2SortedVariable
    , unparse2SortedVariable1
    -- * Concrete
    , Concrete
    , Void
    , toVoid
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import Control.Lens
    ( Iso'
    , Lens
    , Lens'
    )
import qualified Control.Lens as Lens
import Data.Distributive
    ( Distributive (..)
    )
import Data.Functor.Adjunction
    ( Adjunction (..)
    , extractL
    , indexAdjunction
    , tabulateAdjunction
    )
import Data.Functor.Rep
    ( Representable (..)
    )
import Data.Generics.Product
    ( field
    )
import Data.Generics.Sum
    ( _Ctor
    )
import qualified Data.Text as Text
import Data.Void
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Numeric.Natural

import Data.Sup
import Kore.Debug
import Kore.Sort
import Kore.Unparser
import qualified Pretty

{-|'Variable' corresponds to the @variable@ syntactic category from the
Semantics of K, Section 9.1.4 (Patterns).

Particularly, this is the type of variable in patterns returned by the parser.

-}
-- Invariant [variableCounter = Just Sup]:
-- No function returns a value that would match the pattern:
--
-- > Variable { variableCounter = Just Sup }
--
-- This value of variableCounter may only be used in refreshVariable to pivot
-- the set of variables that must not be captured.
data Variable = Variable
    { variableName :: !Id
    , variableCounter :: !(Maybe (Sup Natural))
    , variableSort :: !Sort
    }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable Variable

instance NFData Variable

instance SOP.Generic Variable

instance SOP.HasDatatypeInfo Variable

instance Debug Variable

instance Diff Variable

instance Unparse Variable where
    unparse Variable { variableName, variableCounter, variableSort } =
        unparse variableName
        <> Pretty.pretty variableCounter
        <> Pretty.colon
        <> unparse variableSort

    unparse2 Variable { variableName, variableCounter } =
        unparse2 variableName
        <> Pretty.pretty variableCounter

instance From Variable Variable where
    from = id
    {-# INLINE from #-}

instance From VariableName VariableName where
    from = id
    {-# INLINE from #-}

instance NamedVariable Variable where
    type VariableNameOf Variable = VariableName

    isoVariable1 =
        Lens.iso to fr
      where
        to Variable { variableName, variableCounter, variableSort } =
            Variable1
            { variableName1 =
                VariableName
                { base = variableName
                , counter = variableCounter
                }
            , variableSort1 = variableSort
            }
        fr Variable1 { variableName1, variableSort1 } =
            Variable
            { variableName = base
            , variableCounter = counter
            , variableSort = variableSort1
            }
          where
            VariableName { base, counter } = variableName1

instance VariableBase Variable

{- | Is the variable original (as opposed to generated)?
 -}
isOriginalVariable :: Variable -> Bool
isOriginalVariable Variable { variableCounter } = isNothing variableCounter

{- | Error thrown when 'variableCounter' takes an illegal value.
 -}
illegalVariableCounter :: a
illegalVariableCounter =
    error "Illegal use of Variable { variableCounter = Just Sup }"

{- | Reset 'variableCounter' so that a 'Variable' may be unparsed.

@externalizeFreshVariable@ is not injective and is unsafe if used with
'mapVariables'. See 'Kore.Internal.Pattern.externalizeFreshVariables' instead.

 -}
externalizeFreshVariable :: Variable -> Variable
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

{- | 'NamedVariable' is the name of a Kore variable.

A 'NamedVariable' has instances:

* @'From' variable 'Variable'@
* @'From' 'Variable' variable@

such that both implementations of 'from' are injective,

prop> (==) (fromVariable x) (fromVariable y) === (==) x y

prop> (==) x y === (==) (toVariable x) (toVariable y)

 -}
class
    (Ord variable, Ord (VariableNameOf variable), From (VariableNameOf variable) VariableName, From variable Variable, SortedVariable variable)
    => NamedVariable variable
  where
    type VariableNameOf variable

    isoVariable1 :: Iso' variable (Variable1 (VariableNameOf variable))

lensVariableName
    ::  forall variable1 variable2
    .   (NamedVariable variable1, NamedVariable variable2)
    =>  Lens
                            variable1                  variable2
            (VariableNameOf variable1) (VariableNameOf variable2)
lensVariableName f =
    fmap fromVariable1 . field @"variableName1" f . toVariable1

fromVariable1
    :: NamedVariable variable
    => Variable1 (VariableNameOf variable)
    -> variable
fromVariable1 = Lens.review isoVariable1

toVariable1
    :: NamedVariable variable
    => variable
    -> Variable1 (VariableNameOf variable)
toVariable1 = Lens.view isoVariable1

class
    (From Variable variable, From variable Variable) => VariableBase variable

-- | An injection from 'Variable' to any 'NamedVariable'.
fromVariable :: forall variable. From Variable variable => Variable -> variable
fromVariable = from @Variable @variable

-- | An injection from any 'NamedVariable' to 'Variable'.
toVariable :: forall variable. From variable Variable => variable -> Variable
toVariable = from @variable @Variable

fromVariableName
    :: forall variable. From VariableName variable => VariableName -> variable
fromVariableName = from @VariableName @variable

toVariableName
    :: forall variable. From variable VariableName => variable -> VariableName
toVariableName = from @variable @VariableName

{- | 'SortedVariable' is a Kore variable with a known sort.

 -}
class SortedVariable variable where
    lensVariableSort :: Lens' variable Sort

-- | The known 'Sort' of the given variable.
sortedVariableSort :: SortedVariable variable => variable -> Sort
sortedVariableSort = Lens.view lensVariableSort

instance SortedVariable Variable where
    lensVariableSort = field @"variableSort"
    {-# INLINE lensVariableSort #-}

{- | Unparse any 'SortedVariable' in an Applicative Kore binder.

Variables occur without their sorts as subterms in Applicative Kore patterns,
but with their sorts in binders like @\\exists@ and
@\\forall@. @unparse2SortedVariable@ adds the sort ascription to the unparsed
variable for the latter case.

 -}
unparse2SortedVariable
    :: (SortedVariable variable, Unparse variable)
    => variable
    -> Pretty.Doc ann
unparse2SortedVariable variable =
    unparse2 variable <> Pretty.colon <> unparse (sortedVariableSort variable)

{- | Unparse a 'Variable1' in an Applicative Kore binder.

Variables occur without their sorts as subterms in Applicative Kore patterns,
but with their sorts in binders like @\\exists@ and
@\\forall@. @unparse2SortedVariable@ adds the sort ascription to the unparsed
variable for the latter case.

 -}
unparse2SortedVariable1
    :: Unparse variable
    => Variable1 variable
    -> Pretty.Doc ann
unparse2SortedVariable1 Variable1 { variableName1, variableSort1 } =
    unparse2 variableName1 <> Pretty.colon <> unparse variableSort1

{- | @Concrete@ is a variable occuring in a concrete pattern.

Concrete patterns do not contain variables, so this is an uninhabited type
(it has no constructors).

See also: 'Data.Void.Void'

 -}
data Concrete
    deriving (Eq, GHC.Generic, Ord, Read, Show)

instance Hashable Concrete

instance NFData Concrete

instance SOP.Generic Concrete

instance SOP.HasDatatypeInfo Concrete

instance Debug Concrete

instance Diff Concrete

instance Unparse Concrete where
    unparse = \case {}
    unparse2 = \case {}

instance SortedVariable Concrete where
    lensVariableSort _ = \case {}
    {-# INLINE lensVariableSort #-}

instance NamedVariable Concrete where
    type VariableNameOf Concrete = Void
    isoVariable1 =
        Lens.iso
            (\case {})
            (\Variable1 { variableName1 } -> case variableName1 of {})

instance VariableBase Concrete

instance From VariableName Void where
    from = error "Cannot construct a variable in a concrete term!"
    {-# INLINE from #-}

instance From Variable Concrete where
    from = error "Cannot construct a variable in a concrete term!"
    {-# INLINE from #-}

instance From Concrete variable where
    from = \case {}
    {-# INLINE from #-}

-- * Variable names

data VariableName =
    VariableName
    { base :: !Id
    , counter :: !(Maybe (Sup Natural))
    }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)

instance Hashable VariableName

instance NFData VariableName

instance SOP.Generic VariableName

instance SOP.HasDatatypeInfo VariableName

instance Debug VariableName

instance Diff VariableName

instance Unparse VariableName where
    unparse VariableName { base, counter } =
        unparse base <> Pretty.pretty counter

    unparse2 VariableName { base, counter } =
        unparse base <> Pretty.pretty counter

-- * Element variables

newtype ElementVariableName variable =
    ElementVariableName { unElementVariableName :: variable }
    deriving (Eq, Ord, Show)
    deriving (Functor)
    deriving (Foldable, Traversable)
    deriving (GHC.Generic, GHC.Generic1)

instance Semigroup a => Semigroup (ElementVariableName a) where
    (<>) a b = ElementVariableName (on (<>) unElementVariableName a b)
    {-# INLINE (<>) #-}

instance Monoid a => Monoid (ElementVariableName a) where
    mempty = ElementVariableName mempty
    {-# INLINE mempty #-}

instance Applicative ElementVariableName where
    pure = ElementVariableName
    {-# INLINE pure #-}

    (<*>) (ElementVariableName f) (ElementVariableName a) =
        ElementVariableName (f a)
    {-# INLINE (<*>) #-}

instance Distributive ElementVariableName where
    distribute = ElementVariableName . fmap unElementVariableName
    {-# INLINE distribute #-}

instance Hashable variable => Hashable (ElementVariableName variable)

instance NFData variable => NFData (ElementVariableName variable)

instance SOP.Generic (ElementVariableName variable)

instance SOP.HasDatatypeInfo (ElementVariableName variable)

instance Debug variable => Debug (ElementVariableName variable)

instance (Debug variable, Diff variable) => Diff (ElementVariableName variable)

instance Unparse variable => Unparse (ElementVariableName variable) where
    unparse = unparseGeneric
    {-# INLINE unparse #-}

    unparse2 = unparse2Generic
    {-# INLINE unparse2 #-}

-- * Set variables

instance
    From variable VariableName
    => From (ElementVariableName variable) VariableName
  where
    from = from . unElementVariableName

newtype SetVariableName variable =
    SetVariableName { unSetVariableName :: variable }
    deriving (Eq, Ord, Show)
    deriving (Functor)
    deriving (Foldable, Traversable)
    deriving (GHC.Generic, GHC.Generic1)

instance Semigroup a => Semigroup (SetVariableName a) where
    (<>) a b = SetVariableName (on (<>) unSetVariableName a b)

instance Monoid a => Monoid (SetVariableName a) where
    mempty = SetVariableName mempty
    {-# INLINE mempty #-}

instance Applicative SetVariableName where
    pure = SetVariableName
    {-# INLINE pure #-}

    (<*>) (SetVariableName f) (SetVariableName a) =
        SetVariableName (f a)
    {-# INLINE (<*>) #-}

instance Distributive SetVariableName where
    distribute = SetVariableName . fmap unSetVariableName
    {-# INLINE distribute #-}

instance Hashable variable => Hashable (SetVariableName variable)

instance NFData variable => NFData (SetVariableName variable)

instance SOP.Generic (SetVariableName variable)

instance SOP.HasDatatypeInfo (SetVariableName variable)

instance Debug variable => Debug (SetVariableName variable)

instance (Debug variable, Diff variable) => Diff (SetVariableName variable)

instance Unparse variable => Unparse (SetVariableName variable) where
    unparse = unparseGeneric
    {-# INLINE unparse #-}

    unparse2 = unparse2Generic
    {-# INLINE unparse2 #-}

instance
    From variable VariableName => From (SetVariableName variable) VariableName
  where
    from = from . unSetVariableName

-- * Variable occurrences

{- | @Variable1@ is an occurrence of a variable in a Kore pattern.

The @variable@ parameter is the type of variable names.

Every occurrence of a variable carries the 'Sort' of the variable.

 -}
data Variable1 variable =
    Variable1
    { variableName1 :: !variable
    , variableSort1 :: !Sort
    }
    deriving (Eq, Ord, Show)
    deriving (Functor)
    deriving (Foldable, Traversable)
    deriving (GHC.Generic)

instance Hashable variable => Hashable (Variable1 variable)

instance NFData variable => NFData (Variable1 variable)

instance SOP.Generic (Variable1 variable)

instance SOP.HasDatatypeInfo (Variable1 variable)

instance Debug variable => Debug (Variable1 variable)

instance (Debug variable, Diff variable) => Diff (Variable1 variable)

instance Unparse variable => Unparse (Variable1 variable) where
    unparse Variable1 { variableName1, variableSort1 } =
        unparse variableName1
        <> Pretty.colon
        <> unparse variableSort1

    unparse2 Variable1 { variableName1 } = unparse2 variableName1

{- | @SomeVariableName@ is the name of a variable in a pattern.

@SomeVariableName@ may be an 'ElementVariableName' or a 'SetVariableName'.

 -}
data SomeVariableName variable
    = SomeVariableNameElement !(ElementVariableName variable)
    | SomeVariableNameSet     !(SetVariableName     variable)
    deriving (Eq, Ord, Show)
    deriving (Functor)
    deriving (Foldable, Traversable)
    deriving (GHC.Generic)

instance Hashable variable => Hashable (SomeVariableName variable)

instance NFData variable => NFData (SomeVariableName variable)

instance SOP.Generic (SomeVariableName variable)

instance SOP.HasDatatypeInfo (SomeVariableName variable)

instance Debug variable => Debug (SomeVariableName variable)

instance (Debug variable, Diff variable) => Diff (SomeVariableName variable)

instance Unparse variable => Unparse (SomeVariableName variable) where
    unparse = unparseGeneric
    {-# INLINE unparse #-}

    unparse2 = unparse2Generic
    {-# INLINE unparse2 #-}

instance
    Injection (SomeVariableName variable) (ElementVariableName variable)
  where
    injection = _Ctor @"SomeVariableNameElement"
    {-# INLINE injection #-}

instance
    Injection (SomeVariableName variable) (SetVariableName variable)
  where
    injection = _Ctor @"SomeVariableNameSet"
    {-# INLINE injection #-}

instance
    From variable VariableName => From (SomeVariableName variable) VariableName
  where
    from = extractL . fmap from

{- | 'AdjSomeVariableName' is the right adjoint of 'SomeVariableName'.

The fields of product type 'AdjSomeVariableName' align with the constructors of
sum type 'SomeVariableName'.

In practice, 'AdjSomeVariableName' are used to represent mappings that
transform 'ElementVariableName' and 'SetVariableName' separately while
preserving each kind of variable. For example, the type
@
    'AdjSomeVariableName' (a -> b)
@
is a restriction of the type
@
    'SomeVariableName' a -> 'SomeVariableName' b
@
where the former ensures that (element, set) variables are mapped to (element,
set) variables respectively.

'AdjSomeVariableName' may be constructed and composed through its 'Applicative'
instance. @'pure' x@ constructs an 'AdjSomeVariableName' with the same value @x@
in both fields. @f '<*>' a@ composes two 'AdjSomeVariableName' by applying the
function in each field of @f@ to the value in the corresponding field of @a@.

 -}
data AdjSomeVariableName a =
    AdjSomeVariableName
    { adjSomeVariableNameElement :: ElementVariableName a
    -- ^ compare to: 'SomeVariableNameElement'
    , adjSomeVariableNameSet     :: SetVariableName     a
    -- ^ compare to: 'SomeVariableNameSet'
    }
    deriving (Functor)
    deriving (GHC.Generic1)

instance Semigroup a => Semigroup (AdjSomeVariableName a) where
    (<>) a b =
        AdjSomeVariableName
        { adjSomeVariableNameElement = on (<>) adjSomeVariableNameElement a b
        , adjSomeVariableNameSet = on (<>) adjSomeVariableNameSet a b
        }
    {-# INLINE (<>) #-}

instance Monoid a => Monoid (AdjSomeVariableName a) where
    mempty =
        AdjSomeVariableName
        { adjSomeVariableNameElement = mempty
        , adjSomeVariableNameSet = mempty
        }
    {-# INLINE mempty #-}

instance Applicative AdjSomeVariableName where
    pure a = AdjSomeVariableName (ElementVariableName a) (SetVariableName a)
    {-# INLINE pure #-}

    (<*>) fs as =
        AdjSomeVariableName
        { adjSomeVariableNameElement =
            adjSomeVariableNameElement fs <*> adjSomeVariableNameElement as
        , adjSomeVariableNameSet =
            adjSomeVariableNameSet fs <*> adjSomeVariableNameSet as
        }
    {-# INLINE (<*>) #-}

instance Distributive AdjSomeVariableName where
    distribute f =
        AdjSomeVariableName
        { adjSomeVariableNameElement = collect adjSomeVariableNameElement f
        , adjSomeVariableNameSet = collect adjSomeVariableNameSet f
        }
    {-# INLINE distribute #-}

instance Representable AdjSomeVariableName where
    type Rep AdjSomeVariableName = SomeVariableName ()
    tabulate = tabulateAdjunction
    index = indexAdjunction

instance Adjunction SomeVariableName AdjSomeVariableName where
    unit a =
        AdjSomeVariableName
            (pure . SomeVariableNameElement . pure $ a)
            (pure . SomeVariableNameSet . pure $ a)
    {-# INLINE unit #-}

    counit (SomeVariableNameElement adj) =
        unElementVariableName
        . adjSomeVariableNameElement
        . unElementVariableName
        $ adj
    counit (SomeVariableNameSet adj) =
        unSetVariableName
        . adjSomeVariableNameSet
        . unSetVariableName
        $ adj
    {-# INLINE counit #-}

mapSomeVariableName
    :: AdjSomeVariableName (variable1 -> variable2)
    -> SomeVariableName variable1 -> SomeVariableName variable2
mapSomeVariableName adj variable1 =
    fmap (index adj idx) variable1
  where
    idx = () <$ variable1

mapElementVariableName
    :: AdjSomeVariableName (variable1 -> variable2)
    -> ElementVariableName variable1
    -> ElementVariableName variable2
mapElementVariableName adj =
    (<*>) (adjSomeVariableNameElement adj)

mapSetVariableName
    :: AdjSomeVariableName (variable1 -> variable2)
    -> SetVariableName variable1
    -> SetVariableName variable2
mapSetVariableName adj =
    (<*>) (adjSomeVariableNameSet adj)

traverseSomeVariableName
    :: Applicative f
    => AdjSomeVariableName (variable1 -> f variable2)
    -> SomeVariableName variable1 -> f (SomeVariableName variable2)
traverseSomeVariableName adj variable1 =
    traverse (index adj idx) variable1
  where
    idx = () <$ variable1

traverseElementVariableName
    :: forall variable1 variable2 f
    .  Applicative f
    => AdjSomeVariableName (variable1 -> f variable2)
    -> ElementVariableName variable1
    -> f (ElementVariableName variable2)
traverseElementVariableName adj =
    sequenceA . (<*>) (adjSomeVariableNameElement adj)

traverseSetVariableName
    :: Applicative f
    => AdjSomeVariableName (variable1 -> f variable2)
    -> SetVariableName variable1
    -> f (SetVariableName variable2)
traverseSetVariableName adj =
    sequenceA . (<*>) (adjSomeVariableNameSet adj)

toVoid :: any -> Maybe Void
toVoid = const Nothing

type SomeVariable1 variable = Variable1 (SomeVariableName variable)

type ElementVariable1 variable = Variable1 (ElementVariableName variable)

type SetVariable1 variable = Variable1 (SetVariableName variable)
