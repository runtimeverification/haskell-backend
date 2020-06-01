{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Variables.UnifiedVariable
    ( isElemVar
    , expectElemVar
    , isSetVar
    , expectSetVar
    , extractElementVariable
    , mapSomeVariable1
    , traverseSomeVariable1
    , module Kore.Syntax.Variable
    ) where

import Prelude.Kore

import Kore.Syntax.Variable

isElemVar :: forall variable. SomeVariable1 variable -> Bool
isElemVar unifiedVariable
  | Just _ <- retract @_ @(ElementVariable variable) unifiedVariable = True
  | otherwise                                                        = False

{- | Extract an 'ElementVariable' from a 'SomeVariable1'.

It is an error if the 'SomeVariable1' is not the 'ElemVar' constructor.

Use @expectElemVar@ when maintaining the invariant outside the type system that
the 'SomeVariable1' is an 'ElementVariable', but please include a comment at
the call site describing how the invariant is maintained.

 -}
expectElemVar
    :: HasCallStack
    => SomeVariable1 variable
    -> ElementVariable variable
expectElemVar unifiedVariable
  | Just elementVariable <- retract unifiedVariable = elementVariable
  | otherwise = error "Expected element variable"

isSetVar :: forall variable. SomeVariable1 variable -> Bool
isSetVar unifiedVariable
  | Just _ <- retract @_ @(SetVariable variable) unifiedVariable = True
  | otherwise                                                    = False

{- | Extract an 'SetVariable' from a 'SomeVariable1'.

It is an error if the 'SomeVariable1' is not the 'SetVar' constructor.

Use @expectSetVar@ when maintaining the invariant outside the type system that
the 'SomeVariable1' is an 'SetVariable', but please include a comment at
the call site describing how the invariant is maintained.

 -}
expectSetVar
    :: HasCallStack
    => SomeVariable1 variable
    -> SetVariable variable
expectSetVar unifiedVariable
  | Just setVariable <- retract unifiedVariable = setVariable
  | otherwise = error "Expected set variable"

extractElementVariable
    :: SomeVariable1 variable -> Maybe (ElementVariable variable)
extractElementVariable = retract

mapSomeVariable1
    :: AdjSomeVariableName (variable1 -> variable2)
    -> SomeVariable1 variable1 -> SomeVariable1 variable2
mapSomeVariable1 adj = fmap (mapSomeVariableName adj)

traverseSomeVariable1
    :: Applicative f
    => AdjSomeVariableName (variable1 -> f variable2)
    -> SomeVariable1 variable1 -> f (SomeVariable1 variable2)
traverseSomeVariable1 adj = traverse (traverseSomeVariableName adj)
