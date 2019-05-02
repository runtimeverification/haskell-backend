module Test.Kore.Attribute.Pattern where

import Hedgehog

import Control.Comonad

import           Kore.Attribute.Pattern
import qualified Kore.Variables.Free as Variables.Free

import Test.Kore

-- | Check that the smart constructors in "Kore.AST.Valid" produce the same free
-- variables as 'Variables.Free.freePureVariables'.
hprop_freeVariables :: Property
hprop_freeVariables = property $ do
    termLike <- forAll termLikeGen
    let Pattern { freeVariables } = extract termLike
    freeVariables === Variables.Free.freePureVariables termLike
