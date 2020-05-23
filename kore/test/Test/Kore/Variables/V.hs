module Test.Kore.Variables.V
    ( V (..), mkV, var'
    , sortVariable
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Generics.Product
    ( field
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Numeric.Natural

import Data.Sup
import Debug
import Kore.Internal.TermLike
import Kore.Unparser
import Kore.Variables.Fresh
import Pretty

data V =
    V { value :: Integer, counter :: Maybe (Sup Natural) }
    deriving (Show, Eq, Ord, GHC.Generic)

mkV :: Integer -> V
mkV value = V { value, counter = Nothing }

instance Hashable V

instance SOP.Generic V

instance SOP.HasDatatypeInfo V

instance Debug V

instance Diff V

instance Unparse V where
    unparse (V n _) = "V" <> pretty n <> ":" <> unparse sortVariable
    unparse2 = undefined

instance SortedVariable V where
    lensVariableSort = Lens.lens (const sortVariable) const
    {-# INLINE lensVariableSort #-}

instance From Variable V where
    from = error "Not implemented"

instance From V Variable where
    from = error "Not implemented"

instance NamedVariable V where
    type VariableNameOf V = V

    isoVariable1 =
        Lens.iso to fr
      where
        to variableName1 =
            Variable1 { variableName1, variableSort1 = sortVariable }
        fr Variable1 { variableName1 } = variableName1

instance FreshPartialOrd V where
    infVariable v = v { counter = Nothing }
    supVariable v = v { counter = Just Sup }
    nextVariable =
        Lens.over (field @"counter") increment
      where
        increment =
            \case
                Nothing -> Just (Element 0)
                Just (Element a) -> Just (Element (succ a))
                Just Sup -> illegalVariableCounter

instance FreshVariable V

instance SubstitutionOrd V where
    compareSubstitution = compare

instance VariableBase V

var' :: Integer -> TermLike V
var' = mkElemVar . ElementVariable . mkV

sortVariable :: Sort
sortVariable = SortVariableSort (SortVariable (Id "#a" AstLocationTest))
