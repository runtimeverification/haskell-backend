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
    ) where

import qualified Control.Monad as Monad
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Concrete@ represents the @concrete@ attribute for axioms.
 -}
newtype Concrete = Concrete { isConcrete :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Concrete

instance SOP.HasDatatypeInfo Concrete

instance Debug Concrete

instance Diff Concrete

instance NFData Concrete

instance Default Concrete where
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

instance ParseAttributes Concrete where
    parseAttribute =
        withApplication' $ \params args Concrete { isConcrete } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isConcrete failDuplicate'
            return Concrete { isConcrete = True }
      where
        withApplication' = Parser.withApplication concreteId
        failDuplicate' = Parser.failDuplicate concreteId

    toAttributes Concrete { isConcrete } =
        Attributes [concreteAttribute | isConcrete]
