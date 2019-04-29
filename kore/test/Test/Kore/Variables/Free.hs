module Test.Kore.Variables.Free where

import Hedgehog

import qualified Kore.Annotation as Annotation
import qualified Kore.Annotation.Valid as Annotation.Valid
import           Kore.Step.TermLike
import qualified Kore.Variables.Free as Variables.Free

import Test.Kore

-- | Check that 'Variables.Free.synthetic' produces the same free variable
-- annotations as the smart constructors in "Kore.AST.Valid".
hprop_synthetic :: Property
hprop_synthetic = property $ do
    termLike <- forAll (termLikeGen @Object)
    (===)
        (Annotation.synthesize Variables.Free.synthetic termLike)
        (Annotation.Valid.freeVariables <$> termLike)
