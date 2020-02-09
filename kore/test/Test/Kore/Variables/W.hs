module Test.Kore.Variables.W
    ( W, mkW, war'
    , showVar
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Numeric.Natural

import Data.Sup
import Debug
import Kore.Internal.TermLike
import Kore.Unparser
import Kore.Variables.Fresh
import Pretty

import Test.Kore.Variables.V

data W = W { value :: String, counter :: Maybe (Sup Natural) }
    deriving (Show, Eq, Ord, GHC.Generic)

mkW :: String -> W
mkW value = W { value, counter = Nothing }

instance SOP.Generic W

instance SOP.HasDatatypeInfo W

instance Debug W

instance Diff W

instance Unparse W where
    unparse (W name _) = "W" <> pretty name <> ":" <> unparse sortVariable
    unparse2 = undefined

instance SortedVariable W where
    sortedVariableSort _ = sortVariable

instance From Variable W where
    from = error "Not implemented"

instance From W Variable where
    from = error "Not implemented"

instance VariableName W

instance FreshPartialOrd W where
    compareFresh (W a an) (W b bn)
      | a == b = Just (compare an bn)
      | otherwise = Nothing
    supVariable w = w { counter = Just Sup }
    nextVariable w W { counter } =
        w { counter = counter' }
      where
        counter' =
            case counter of
                Nothing -> Just (Element 0)
                Just (Element a) -> Just (Element (succ a))
                Just Sup -> illegalVariableCounter

instance FreshVariable W

instance SubstitutionOrd W where
    compareSubstitution = compare

showVar :: V -> W
showVar (V i n) = W (show i) n

war' :: String -> TermLike W
war' = mkElemVar . ElementVariable . mkW
