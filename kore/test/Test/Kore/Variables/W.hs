module Test.Kore.Variables.W (
    W,
    mkW,
    war',
    showVar,
    showUnifiedVar,
) where

import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import Data.Sup
import Debug
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Internal.TermLike
import Kore.Unparser
import Kore.Variables.Fresh
import Numeric.Natural
import Prelude.Kore
import Pretty
import Test.Kore.Variables.V

data W = W {value :: String, counter :: Maybe (Sup Natural)}
    deriving stock (Show, Eq, Ord)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

mkW :: String -> Variable W
mkW value =
    Variable
        { variableName = W{value, counter = Nothing}
        , variableSort = sortVariable
        }

instance Unparse W where
    unparse (W name _) = "W" <> pretty name <> ":" <> unparse sortVariable
    unparse2 = undefined

instance From VariableName W where
    from = error "Not implemented"

instance From W VariableName where
    from = error "Not implemented"

instance FreshPartialOrd W where
    minBoundName w = w{counter = Nothing}
    maxBoundName w = w{counter = Just Sup}
    nextName w1 w2 =
        Just $ Lens.set (field @"counter") counter' w1
      where
        counter' =
            case Lens.view (field @"counter") w2 of
                Nothing -> Just (Element 0)
                Just (Element a) -> Just (Element (succ a))
                Just Sup -> illegalVariableCounter

instance FreshName W

instance SubstitutionOrd W where
    compareSubstitution = compare

showVar :: V -> W
showVar (V i n) = W (show i) n

showUnifiedVar :: AdjSomeVariableName (V -> W)
showUnifiedVar = pure showVar

war' :: String -> TermLike W
war' = mkElemVar . fmap ElementVariableName . mkW
