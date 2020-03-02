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

import qualified Data.Set as Set
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Attribute.Pattern.FreeVariables
import Kore.Debug
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Variables.UnifiedVariable
    ( mapUnifiedVariable
    )

{- | @Concrete@ represents the @concrete@ attribute for axioms.
 -}
newtype Concrete variable = Concrete { freeVariables :: FreeVariables variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic (Concrete variable)

instance SOP.HasDatatypeInfo (Concrete variable)

instance Debug variable => Debug (Concrete variable)

instance (Debug variable, Diff variable) => Diff (Concrete variable)

instance NFData variable => NFData (Concrete variable)

instance Default (Concrete variable) where
    def = Concrete def

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
    :: Ord variable
    => AttributePattern
    -> FreeVariables variable
    -> Concrete variable
    -> Parser (Concrete variable)
parseConcreteAttribute
    attribute
    (FreeVariables variables)
    (Concrete (FreeVariables concreteFreeVariables))
  = do
        boolResult <- parseBoolAttribute concreteId attribute isOK
        if boolResult then
            return $ Concrete $ FreeVariables variables
        else
            return def
  where
    isOK = variables `Set.isSubsetOf` concreteFreeVariables

instance From (Concrete variable) Attributes where
    from (Concrete (FreeVariables set)) =
        toBoolAttributes concreteAttribute (Set.null set)

mapConcreteVariables
    :: Ord variable2
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    -> Concrete variable1 -> Concrete variable2
mapConcreteVariables fElemVar fSetVar (Concrete (FreeVariables variables)) =
    Concrete . FreeVariables
    . Set.map (mapUnifiedVariable fElemVar fSetVar)
    $ variables
