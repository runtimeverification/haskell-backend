module Test.Kore.Variables.W
    ( W, mkW, war'
    , showVar
    , showUnifiedVar
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
import Kore.Variables.UnifiedVariable
import Pretty

import Test.Kore.Variables.V

data W = W { value :: String, counter :: Maybe (Sup Natural) }
    deriving (Show, Eq, Ord, GHC.Generic)

mkW :: String -> W
mkW value = W { value, counter = Nothing }

instance Hashable W

instance SOP.Generic W

instance SOP.HasDatatypeInfo W

instance Debug W

instance Diff W

instance Unparse W where
    unparse (W name _) = "W" <> pretty name <> ":" <> unparse sortVariable
    unparse2 = undefined

instance SortedVariable W where
    lensVariableSort = Lens.lens (const sortVariable) const
    {-# INLINE lensVariableSort #-}

instance From Variable W where
    from = error "Not implemented"

instance From W Variable where
    from = error "Not implemented"

instance NamedVariable W where
    type VariableNameOf W = W

    isoVariable1 =
        Lens.iso to fr
      where
        to variableName1 =
            Variable1 { variableName1, variableSort1 = sortVariable }
        fr Variable1 { variableName1 } = variableName1

instance FreshPartialOrd W where
    infVariable w = w { counter = Nothing }
    supVariable w = w { counter = Just Sup }
    nextVariable =
        Lens.over (field @"counter") increment
      where
        increment =
            \case
                Nothing -> Just (Element 0)
                Just (Element a) -> Just (Element (succ a))
                Just Sup -> illegalVariableCounter

instance FreshVariable W

instance SubstitutionOrd W where
    compareSubstitution = compare

instance VariableBase W

showVar :: V -> W
showVar (V i n) = W (show i) n

showUnifiedVar :: AdjUnifiedVariable (V -> W)
showUnifiedVar = pure showVar

war' :: String -> TermLike W
war' = mkElemVar . ElementVariable . mkW
