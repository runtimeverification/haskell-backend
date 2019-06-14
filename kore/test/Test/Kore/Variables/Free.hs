module Test.Kore.Variables.Free where

import Hedgehog

import Data.Set
       ( Set )

import qualified Kore.Attribute.Null as Attribute
import           Kore.Attribute.Pattern.FreeVariables
import qualified Kore.Attribute.Synthetic as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Internal.TermLike
import qualified Kore.Syntax.Pattern as Syntax
import qualified Kore.Variables.Free as Variables.Free

import Test.Kore.Internal.TermLike

-- | Check that 'Variables.Free.synthetic' produces the same free variable
-- annotations as the smart constructors in "Kore.Internal.TermLike".
hprop_synthetic :: Property
hprop_synthetic = property $ do
    termLike <- forAll termLikeGen
    let
        external :: Syntax.Pattern Variable Attribute.Null
        external = Builtin.externalizePattern termLike
        synthesized :: Syntax.Pattern Variable (Set Variable)
        synthesized = Attribute.synthesizeAux Variables.Free.synthetic external
        expect = getFreeVariables (freeVariables termLike)
        actual = extract synthesized
    expect === actual
