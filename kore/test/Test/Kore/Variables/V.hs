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

instance SOP.Generic V

instance SOP.HasDatatypeInfo V

instance Debug V

instance Diff V

instance Unparse V where
    unparse (V n _) = "V" <> pretty n <> ":" <> unparse sortVariable
    unparse2 = undefined

instance SortedVariable V where
    lensVariableSort = Lens.lens (const sortVariable) (\v _ -> v)
    {-# INLINE lensVariableSort #-}

instance From Variable V where
    from = error "Not implemented"

instance From V Variable where
    from = error "Not implemented"

instance VariableName V

instance FreshPartialOrd V where
    compareFresh (V a an) (V b bn)
      | a == b = Just (compare an bn)
      | otherwise = Nothing
    supVariable v = v { counter = Just Sup }
    nextVariable V { counter = bound } =
        field @"counter" (increment . max bound)
      where
        increment =
            \case
                Nothing -> pure $ Just (Element 0)
                Just (Element a) -> pure $ Just (Element (succ a))
                Just Sup -> empty

instance FreshVariable V

instance SubstitutionOrd V where
    compareSubstitution = compare

var' :: Integer -> TermLike V
var' = mkElemVar . ElementVariable . mkV

sortVariable :: Sort
sortVariable = SortVariableSort (SortVariable (Id "#a" AstLocationTest))
