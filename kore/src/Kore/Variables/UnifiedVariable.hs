{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    , ElementVariable (..), SetVariable (..)
    , isElemVar
    , expectElemVar
    , isSetVar
    , expectSetVar
    , extractElementVariable
    , foldMapVariable
    , unifiedVariableSort
    , refreshElementVariable
    , refreshSetVariable
    -- * AdjUnifiedVariable
    , MapVariables
    , AdjUnifiedVariable (..)
    , asConcreteUnifiedVariable
    , fromConcreteUnifiedVariable
    , toUnifiedVariable
    , fromUnifiedVariable
    , mapUnifiedVariable
    , traverseUnifiedVariable
    -- * UnifiedVariableMap
    , VariableMap
    , UnifiedVariableMap
    , renameElementVariable, renameSetVariable
    , lookupRenamedElementVariable, lookupRenamedSetVariable
    -- * Re-exports
    , Kleisli (..)
    ) where

import Prelude.Kore

import Control.Arrow
    ( Kleisli (..)
    )
import Control.DeepSeq
    ( NFData
    )
import qualified Control.Lens as Lens
import Data.Functor.Const
import Data.Generics.Product
    ( field
    )
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Generics.SOP as SOP
import GHC.Generics
    ( Generic
    )

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
import Kore.Unparser
import Kore.Variables.Fresh

{- | @UnifiedVariable@ helps distinguish set variables (introduced by 'SetVar')
from element variables (introduced by 'ElemVar').
 -}
data UnifiedVariable variable
    = ElemVar !(ElementVariable variable)
    | SetVar  !(SetVariable variable)
    deriving (Eq, Ord, Show)
    deriving (Generic)

instance NFData variable => NFData (UnifiedVariable variable)

instance SOP.Generic (UnifiedVariable variable)

instance SOP.HasDatatypeInfo (UnifiedVariable variable)

instance Debug variable => Debug (UnifiedVariable variable)

instance (Debug variable, Diff variable) => Diff (UnifiedVariable variable)

instance Hashable variable => Hashable (UnifiedVariable variable)

instance Unparse variable => Unparse (UnifiedVariable variable) where
    unparse = foldMapVariable unparse
    unparse2 = foldMapVariable unparse2

instance
    SortedVariable variable
    => SortedVariable (UnifiedVariable variable)
  where
    lensVariableSort f =
        \case
            ElemVar elemVar -> ElemVar <$> lensVariableSort f elemVar
            SetVar setVar -> SetVar <$> lensVariableSort f setVar
    {-# INLINE lensVariableSort #-}

instance From (UnifiedVariable variable) variable where
    from (ElemVar elementVariable) = getElementVariable elementVariable
    from (SetVar setVariable) = getSetVariable setVariable
    {-# INLINE from #-}

instance
    From variable Variable => From (UnifiedVariable variable) Variable
  where
    from (ElemVar elementVariable) = from elementVariable
    from (SetVar setVariable) = from setVariable
    {-# INLINE from #-}

instance
    NamedVariable variable => NamedVariable (UnifiedVariable variable)
  where
    type VariableNameOf (UnifiedVariable variable) =
        SomeVariableName (VariableNameOf variable)

    lensVariableName =
        Lens.lens get set
      where
        get (ElemVar elementVariable) =
            SomeVariableNameElement (Lens.view lensVariableName elementVariable)
        get (SetVar setVariable) =
            SomeVariableNameSet (Lens.view lensVariableName setVariable)
        set unifiedVariable someVariableName =
            case someVariableName of
                SomeVariableNameElement elementVariableName ->
                    ElementVariable variable
                    & Lens.set lensVariableName elementVariableName
                    & ElemVar
                SomeVariableNameSet setVariableName ->
                    SetVariable variable
                    & Lens.set lensVariableName setVariableName
                    & SetVar
          where
            variable = from @_ @variable unifiedVariable

    isoVariable1 =
        Lens.iso to fr
      where
        to (ElemVar elementVariable) =
            SomeVariableNameElement <$> Lens.view isoVariable1 elementVariable
        to (SetVar setVariable) =
            SomeVariableNameSet <$> Lens.view isoVariable1 setVariable
        fr Variable1 { variableName1, variableSort1 } =
            case variableName1 of
                SomeVariableNameElement elementVariableName ->
                    Variable1
                    { variableName1 = elementVariableName
                    , variableSort1
                    }
                    & Lens.review isoVariable1
                    & ElemVar
                SomeVariableNameSet setVariableName ->
                    Variable1
                    { variableName1 = setVariableName
                    , variableSort1
                    }
                    & Lens.review isoVariable1
                    & SetVar

instance
    FreshPartialOrd variable => FreshPartialOrd (UnifiedVariable variable)
  where
    infVariable =
        \case
            ElemVar elemVar -> ElemVar (infVariable elemVar)
            SetVar setVar -> SetVar (infVariable setVar)
    {-# INLINE infVariable #-}

    supVariable =
        \case
            ElemVar elemVar -> ElemVar (supVariable elemVar)
            SetVar setVar -> SetVar (supVariable setVar)
    {-# INLINE supVariable #-}

    nextVariable =
        \case
            ElemVar elemVar -> ElemVar (nextVariable elemVar)
            SetVar setVar -> SetVar (nextVariable setVar)
    {-# INLINE nextVariable #-}

instance
    (FreshPartialOrd variable, SortedVariable variable)
    => FreshVariable (UnifiedVariable variable)

instance From from to => From (UnifiedVariable from) (UnifiedVariable to) where
    from (ElemVar var) = ElemVar (from var)
    from (SetVar var) = SetVar (from var)

isElemVar :: UnifiedVariable variable -> Bool
isElemVar (ElemVar _) = True
isElemVar _ = False

{- | Extract an 'ElementVariable' from a 'UnifiedVariable'.

It is an error if the 'UnifiedVariable' is not the 'ElemVar' constructor.

Use @expectElemVar@ when maintaining the invariant outside the type system that
the 'UnifiedVariable' is an 'ElementVariable', but please include a comment at
the call site describing how the invariant is maintained.

 -}
expectElemVar
    :: HasCallStack
    => UnifiedVariable variable
    -> ElementVariable variable
expectElemVar (ElemVar elementVariable) = elementVariable
expectElemVar _ = error "Expected element variable"

isSetVar :: UnifiedVariable variable -> Bool
isSetVar (SetVar _) = True
isSetVar _ = False

{- | Extract an 'SetVariable' from a 'UnifiedVariable'.

It is an error if the 'UnifiedVariable' is not the 'SetVar' constructor.

Use @expectSetVar@ when maintaining the invariant outside the type system that
the 'UnifiedVariable' is an 'SetVariable', but please include a comment at
the call site describing how the invariant is maintained.

 -}
expectSetVar
    :: HasCallStack
    => UnifiedVariable variable
    -> SetVariable variable
expectSetVar (SetVar setVariable) = setVariable
expectSetVar _ = error "Expected set variable"

instance
    SortedVariable variable =>
    Synthetic Sort (Const (UnifiedVariable variable))
  where
    synthetic (Const var) = foldMapVariable sortedVariableSort var
    {-# INLINE synthetic #-}

extractElementVariable
    :: UnifiedVariable variable -> Maybe (ElementVariable variable)
extractElementVariable (ElemVar var) = Just var
extractElementVariable _ = Nothing

-- |Meant for extracting variable-related information from a 'UnifiedVariable'
foldMapVariable :: (variable -> a) -> UnifiedVariable variable -> a
foldMapVariable f (ElemVar v) = f (getElementVariable v)
foldMapVariable f (SetVar v) = f (getSetVariable v)

-- | The 'Sort' of a 'SetVariable' or an 'ElementVariable'.
unifiedVariableSort
    :: SortedVariable variable
    => UnifiedVariable variable
    -> Sort
unifiedVariableSort = foldMapVariable sortedVariableSort

refreshElementVariable
    :: FreshVariable (UnifiedVariable variable)
    => Set (UnifiedVariable variable)
    -> ElementVariable variable
    -> Maybe (ElementVariable variable)
refreshElementVariable avoiding =
    -- expectElemVar is safe because the FreshVariable instance of
    -- UnifiedVariable (above) conserves the ElemVar constructor.
    fmap expectElemVar . refreshVariable avoiding . ElemVar

refreshSetVariable
    :: FreshVariable (UnifiedVariable variable)
    => Set (UnifiedVariable variable)
    -> SetVariable variable
    -> Maybe (SetVariable variable)
refreshSetVariable avoiding =
    -- expectElemVar is safe because the FreshVariable instance of
    -- UnifiedVariable (above) conserves the SetVar constructor.
    fmap expectSetVar . refreshVariable avoiding . SetVar

type MapVariables variable1 variable2 term1 term2 =
    AdjUnifiedVariable (variable1 -> variable2) -> term1 -> term2

{- | 'AdjUnifiedVariable' is the right adjoint of 'UnifiedVariable'.

Where 'UnifiedVariable' is a sum type, 'AdjUnifiedVariable' is a product type
with one field for each constructor. A 'UnifiedVariable' can be used to select
one field from the 'AdjUnifiedVariable'.

In practice, 'AdjUnifiedVariable' are used to represent morphisms that transform
'ElementVariable' and 'SetVariable' separately while preserving each kind of
variable; that is, the type @'AdjUnifiedVariable' (a -> b)@ is a restriction of
the type @'UnifiedVariable' a -> 'UnifiedVariable' b@

 -}
data AdjUnifiedVariable a =
    AdjUnifiedVariable
    { elemVar :: ElementVariable a
    , setVar  :: SetVariable     a
    }
    deriving (Functor)

instance Applicative AdjUnifiedVariable where
    pure a = AdjUnifiedVariable (ElementVariable a) (SetVariable a)
    {-# INLINE pure #-}

    (<*>) fs as =
        AdjUnifiedVariable
        { elemVar = elemVar fs <*> elemVar as
        , setVar = setVar fs <*> setVar as
        }
    {-# INLINE (<*>) #-}

asConcreteUnifiedVariable :: AdjUnifiedVariable (variable -> Maybe Concrete)
asConcreteUnifiedVariable = pure (const Nothing)

fromConcreteUnifiedVariable :: AdjUnifiedVariable (Concrete -> variable)
fromConcreteUnifiedVariable = pure (\case {})

mapUnifiedVariable
    :: AdjUnifiedVariable (variable1 -> variable2)
    -> UnifiedVariable variable1 -> UnifiedVariable variable2
mapUnifiedVariable AdjUnifiedVariable { elemVar, setVar } =
    \case
        ElemVar elementVariable -> ElemVar $ elemVar <*> elementVariable
        SetVar setVariable -> SetVar $ setVar <*> setVariable

traverseUnifiedVariable
    :: Applicative f
    => AdjUnifiedVariable (variable1 -> f variable2)
    -> UnifiedVariable variable1 -> f (UnifiedVariable variable2)
traverseUnifiedVariable AdjUnifiedVariable { elemVar, setVar } =
    \case
        ElemVar elementVariable ->
            ElemVar <$> sequenceA (elemVar <*> elementVariable)
        SetVar setVariable ->
            SetVar <$> sequenceA (setVar <*> setVariable)

toUnifiedVariable
    :: NamedVariable variable
    => AdjUnifiedVariable (variable -> Variable)
toUnifiedVariable = pure toVariable

fromUnifiedVariable
    :: From Variable variable
    => AdjUnifiedVariable (Variable -> variable)
fromUnifiedVariable = pure fromVariable

type VariableMap meta variable1 variable2 =
    Map (meta variable1) (meta variable2)

data UnifiedVariableMap variable1 variable2 =
    UnifiedVariableMap
        { setVariables
            :: !(VariableMap SetVariable variable1 variable2)
        , elementVariables
            :: !(VariableMap ElementVariable variable1 variable2)
        }
    deriving (Generic)

instance
    Ord variable1 => Semigroup (UnifiedVariableMap variable1 variable2)
  where
    (<>) a b =
        UnifiedVariableMap
            { setVariables = on (<>) setVariables a b
            , elementVariables = on (<>) elementVariables a b
            }
    {-# INLINE (<>) #-}

instance Ord variable1 => Monoid (UnifiedVariableMap variable1 variable2) where
    mempty = UnifiedVariableMap mempty mempty
    {-# INLINE mempty #-}

renameSetVariable
    :: Ord variable1
    => SetVariable variable1
    -> SetVariable variable2
    -> UnifiedVariableMap variable1 variable2
    -> UnifiedVariableMap variable1 variable2
renameSetVariable variable1 variable2 =
    Lens.over
        (field @"setVariables")
        (Map.insert variable1 variable2)
{-# INLINE renameSetVariable #-}

renameElementVariable
    :: Ord variable1
    => ElementVariable variable1
    -> ElementVariable variable2
    -> UnifiedVariableMap variable1 variable2
    -> UnifiedVariableMap variable1 variable2
renameElementVariable variable1 variable2 =
    Lens.over
        (field @"elementVariables")
        (Map.insert variable1 variable2)
{-# INLINE renameElementVariable #-}

lookupRenamedElementVariable
    :: Ord variable1
    => ElementVariable variable1
    -> UnifiedVariableMap variable1 variable2
    -> Maybe (ElementVariable variable2)
lookupRenamedElementVariable variable =
    Map.lookup variable . elementVariables
{-# INLINE lookupRenamedElementVariable #-}

lookupRenamedSetVariable
    :: Ord variable1
    => SetVariable variable1
    -> UnifiedVariableMap variable1 variable2
    -> Maybe (SetVariable variable2)
lookupRenamedSetVariable variable =
    Map.lookup variable . setVariables
{-# INLINE lookupRenamedSetVariable #-}
