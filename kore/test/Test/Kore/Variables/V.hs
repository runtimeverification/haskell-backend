module Test.Kore.Variables.V (
    V (..),
    mkV,
    var',
    sortVariable,
) where

import Control.Lens qualified as Lens
import Data.Generics.Product (
    field,
 )
import Data.Sup
import Debug
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Internal.TermLike hiding (counter)
import Kore.Unparser
import Kore.Variables.Fresh hiding (counter)
import Numeric.Natural
import Prelude.Kore
import Pretty

data V = V {value :: Integer, counter :: Maybe (Sup Natural)}
    deriving stock (Show, Eq, Ord)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

mkV :: Integer -> Variable V
mkV value =
    Variable
        { variableName = V{value, counter = Nothing}
        , variableSort = sortVariable
        }

instance Unparse V where
    unparse (V n _) = "V" <> pretty n <> ":" <> unparse sortVariable
    unparse2 = undefined

instance From VariableName V where
    from = error "Not implemented"

instance From V VariableName where
    from = error "Not implemented"

instance FreshPartialOrd V where
    minBoundName v = v{counter = Nothing}
    maxBoundName v = v{counter = Just Sup}
    nextName v1 v2 =
        Just $ Lens.set (field @"counter") counter' v1
      where
        counter' =
            case Lens.view (field @"counter") v2 of
                Nothing -> Just (Element 0)
                Just (Element a) -> Just (Element (succ a))
                Just Sup -> illegalVariableCounter

instance FreshName V

instance SubstitutionOrd V where
    compareSubstitution = compare

var' :: Integer -> TermLike V
var' = mkElemVar . fmap ElementVariableName . mkV

sortVariable :: Sort
sortVariable = SortVariableSort (SortVariable (Id "#a" AstLocationTest))
