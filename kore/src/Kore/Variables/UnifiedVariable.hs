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
    , mapUnifiedVariable
    , traverseUnifiedVariable
    ) where

import Prelude.Kore

import Kore.Syntax.Variable

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
  | Just _ <- retract @_ @(SetVariable variable) unifiedVariable = True
  | otherwise                                                    = False

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

mapUnifiedVariable
    :: AdjSomeVariableName (variable1 -> variable2)
    -> UnifiedVariable variable1 -> UnifiedVariable variable2
mapUnifiedVariable adj = fmap (mapSomeVariableName adj)

traverseUnifiedVariable
    :: Applicative f
    => AdjSomeVariableName (variable1 -> f variable2)
    -> UnifiedVariable variable1 -> f (UnifiedVariable variable2)
traverseUnifiedVariable adj = traverse (traverseSomeVariableName adj)
