{-|
Module      : Kore.Attribute.Axiom.Concrete
Description : Concrete axiom attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com

-}
module Kore.Attribute.Axiom.Concrete
    ( Concrete (..)
    , concreteId, concreteSymbol, concreteAttribute
    , mapConcreteVariables
    , parseConcreteAttribute
    ) where

import Prelude.Kore

import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable

{- | @Concrete@ represents the @concrete@ attribute for axioms.
 -}
newtype Concrete variable = Concrete { isConcrete :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic (Concrete variable)

instance SOP.HasDatatypeInfo (Concrete variable)

instance Debug (Concrete variable)

instance Diff (Concrete variable)

instance NFData (Concrete variable)

instance Default (Concrete variable) where
    def = Concrete False

-- | Kore identifier representing the @concrete@ attribute symbol.
concreteId :: Id
concreteId = "concrete"

-- | Kore symbol representing the @concrete@ attribute.
concreteSymbol :: SymbolOrAlias
concreteSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = concreteId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @concrete@ attribute.
concreteAttribute :: AttributePattern
concreteAttribute = attributePattern_ concreteSymbol

parseConcreteAttribute
    :: AttributePattern
    -> Concrete variable
    -> Parser (Concrete variable)
parseConcreteAttribute = parseBoolAttribute concreteId

instance From (Concrete variable) Attributes where
    from = toBoolAttributes concreteAttribute

mapConcreteVariables
    ::(ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    -> Concrete variable1 -> Concrete variable2
mapConcreteVariables _ _ (Concrete b) = Concrete b
