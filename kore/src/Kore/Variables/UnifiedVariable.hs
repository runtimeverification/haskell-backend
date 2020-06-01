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
    , mapSomeVariable
    , traverseSomeVariable
    , module Kore.Syntax.Variable
    ) where

import Prelude.Kore

import Kore.Syntax.Variable

isElemVar :: forall variable. SomeVariable variable -> Bool
isElemVar unifiedVariable
  | Just _ <- retract @_ @(ElementVariable variable) unifiedVariable = True
  | otherwise                                                        = False

{- | Extract an 'ElementVariable' from a 'SomeVariable'.

It is an error if the 'SomeVariable' is not the 'ElemVar' constructor.

Use @expectElemVar@ when maintaining the invariant outside the type system that
the 'SomeVariable' is an 'ElementVariable', but please include a comment at
the call site describing how the invariant is maintained.

 -}
expectElemVar
    :: HasCallStack
    => SomeVariable variable
    -> ElementVariable variable
expectElemVar unifiedVariable
  | Just elementVariable <- retract unifiedVariable = elementVariable
  | otherwise = error "Expected element variable"

isSetVar :: forall variable. SomeVariable variable -> Bool
isSetVar unifiedVariable
  | Just _ <- retract @_ @(SetVariable variable) unifiedVariable = True
  | otherwise                                                    = False

{- | Extract an 'SetVariable' from a 'SomeVariable'.

It is an error if the 'SomeVariable' is not the 'SetVar' constructor.

Use @expectSetVar@ when maintaining the invariant outside the type system that
the 'SomeVariable' is an 'SetVariable', but please include a comment at
the call site describing how the invariant is maintained.

 -}
expectSetVar
    :: HasCallStack
    => SomeVariable variable
    -> SetVariable variable
expectSetVar unifiedVariable
  | Just setVariable <- retract unifiedVariable = setVariable
  | otherwise = error "Expected set variable"

extractElementVariable
    :: SomeVariable variable -> Maybe (ElementVariable variable)
extractElementVariable = retract

mapSomeVariable
    :: AdjSomeVariableName (variable1 -> variable2)
    -> SomeVariable variable1 -> SomeVariable variable2
mapSomeVariable adj = fmap (mapSomeVariableName adj)

traverseSomeVariable
    :: Applicative f
    => AdjSomeVariableName (variable1 -> f variable2)
    -> SomeVariable variable1 -> f (SomeVariable variable2)
traverseSomeVariable adj = traverse (traverseSomeVariableName adj)
