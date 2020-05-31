{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    , ElementVariable, SetVariable
    , isElemVar
    , expectElemVar
    , isSetVar
    , expectSetVar
    , extractElementVariable
    , foldMapVariable
    , unifiedVariableSort
    , refreshElementVariable
    , refreshSetVariable
    , MapVariables
    , mapUnifiedVariable
    , traverseUnifiedVariable
    ) where

import Prelude.Kore

import Data.Set
    ( Set
    )

import Kore.Sort
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
import Kore.Variables.Fresh

{- | @UnifiedVariable@ helps distinguish set variables (introduced by 'SetVar')
from element variables (introduced by 'ElemVar').
 -}
type UnifiedVariable variable = SomeVariable1 variable

isElemVar :: forall variable. UnifiedVariable variable -> Bool
isElemVar unifiedVariable
  | Just _ <- retract @_ @(ElementVariable variable) unifiedVariable = True
  | otherwise                                                        = False

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
expectElemVar unifiedVariable
  | Just elementVariable <- retract unifiedVariable = elementVariable
  | otherwise = error "Expected element variable"

isSetVar :: forall variable. UnifiedVariable variable -> Bool
isSetVar unifiedVariable
  | Just _ <- retract @_ @(ElementVariable variable) unifiedVariable = True
  | otherwise                                                        = False

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
expectSetVar unifiedVariable
  | Just setVariable <- retract unifiedVariable = setVariable
  | otherwise = error "Expected set variable"

extractElementVariable
    :: UnifiedVariable variable -> Maybe (ElementVariable variable)
extractElementVariable = retract

-- |Meant for extracting variable-related information from a 'UnifiedVariable'
foldMapVariable :: (variable -> a) -> UnifiedVariable variable -> a
foldMapVariable f Variable1 { variableName1 } =
    case variableName1 of
        SomeVariableNameElement elementVariableName ->
            f (unElementVariableName elementVariableName)
        SomeVariableNameSet setVariableName ->
            f (unSetVariableName setVariableName)

-- | The 'Sort' of a 'SetVariable' or an 'ElementVariable'.
unifiedVariableSort :: UnifiedVariable variable -> Sort
unifiedVariableSort = variableSort1

refreshElementVariable
    :: FreshName (SomeVariableName variable)
    => Set (SomeVariableName variable)
    -> ElementVariable variable
    -> Maybe (ElementVariable variable)
refreshElementVariable avoiding =
    -- expectElemVar is safe because the FreshVariable instance of
    -- UnifiedVariable (above) conserves the ElemVar constructor.
    fmap expectElemVar . refreshVariable avoiding . inject

refreshSetVariable
    :: FreshName (SomeVariableName variable)
    => Set (SomeVariableName variable)
    -> SetVariable variable
    -> Maybe (SetVariable variable)
refreshSetVariable avoiding =
    -- expectElemVar is safe because the FreshVariable instance of
    -- UnifiedVariable (above) conserves the SetVar constructor.
    fmap expectSetVar . refreshVariable avoiding . inject

type MapVariables variable1 variable2 term1 term2 =
    AdjSomeVariableName (variable1 -> variable2) -> term1 -> term2

mapUnifiedVariable
    :: AdjSomeVariableName (variable1 -> variable2)
    -> UnifiedVariable variable1 -> UnifiedVariable variable2
mapUnifiedVariable adj = fmap (mapSomeVariableName adj)

traverseUnifiedVariable
    :: Applicative f
    => AdjSomeVariableName (variable1 -> f variable2)
    -> UnifiedVariable variable1 -> f (UnifiedVariable variable2)
traverseUnifiedVariable adj = traverse (traverseSomeVariableName adj)
