{-|
Module      : Kore.Attribute.Axiom.Concrete
Description : Concrete axiom attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com

-}
module Kore.Attribute.Axiom.Concrete
    ( Concrete (..), isConcrete
    , concreteId, concreteSymbol, concreteAttribute
    , mapConcreteVariables
    , parseConcreteAttribute
    -- * Re-exports
    , FreeVariables
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , mapFreeVariables
    , nullFreeVariables
    )
import Kore.Debug
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable

{- | @Concrete@ represents the @concrete@ attribute for axioms.
 -}
newtype Concrete variable =
    Concrete { unConcrete :: FreeVariables variable }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic (Concrete variable)

instance SOP.HasDatatypeInfo (Concrete variable)

instance Debug variable => Debug (Concrete variable)

instance (Debug variable, Diff variable) => Diff (Concrete variable)

instance NFData variable => NFData (Concrete variable)

instance Ord variable => Default (Concrete variable) where
    def = Concrete mempty

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
    :: forall variable
    .  Ord variable
    => FreeVariables variable
    -> AttributePattern
    -> Concrete variable
    -> Parser (Concrete variable)
parseConcreteAttribute freeVariables =
    parseBoolAttributeAux iso concreteId
  where
    iso :: Lens.Iso' (Concrete variable) Bool
    iso =
        Lens.iso
            isConcrete
            (\b -> Concrete $ if b then freeVariables else mempty)

instance From (Concrete variable) Attributes where
    from = toBoolAttributesAux (Lens.to isConcrete) concreteAttribute

mapConcreteVariables
    :: Ord variable2
    => (ElementVariable variable1 -> ElementVariable variable2)
    -> (SetVariable variable1 -> SetVariable variable2)
    ->  Concrete variable1 -> Concrete variable2
mapConcreteVariables mapElemVar mapSetVar (Concrete freeVariables) =
    Concrete (mapFreeVariables mapElemVar mapSetVar freeVariables)

isConcrete :: Concrete variable -> Bool
isConcrete = not . nullFreeVariables . unConcrete
