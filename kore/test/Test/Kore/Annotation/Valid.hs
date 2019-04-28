module Test.Kore.Annotation.Valid where

import Hedgehog

import Control.Comonad

import           Kore.Annotation.Valid
                 ( Valid (..) )
import           Kore.AST.MetaOrObject
                 ( Object )
import qualified Kore.Variables.Free as Variables.Free

import Test.Kore

-- | Check that the smart constructors in "Kore.AST.Valid" produce the same free
-- variables as 'Variables.Free.freePureVariables'.
hprop_freeVariables :: Property
hprop_freeVariables = property $ do
    termLike <- forAll (termLikeGen @Object)
    let Valid { freeVariables } = extract termLike
    freeVariables === Variables.Free.freePureVariables termLike
