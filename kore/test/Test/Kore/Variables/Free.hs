module Test.Kore.Variables.Free where

import Hedgehog

import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Attribute.Synthetic as Attribute
import qualified Kore.Variables.Free as Variables.Free

import Test.Kore

-- | Check that 'Variables.Free.synthetic' produces the same free variable
-- annotations as the smart constructors in "Kore.Internal.TermLike".
hprop_synthetic :: Property
hprop_synthetic = property $ do
    termLike <- forAll termLikeGen
    (===)
        (Attribute.synthesize Variables.Free.synthetic termLike)
        (Attribute.freeVariables <$> termLike)
