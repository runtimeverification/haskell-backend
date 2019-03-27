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

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Monad as Monad
import           Data.Default
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Kore hiding
                 ( Concrete )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

{- | @Concrete@ represents the @concrete@ attribute for axioms.
 -}
newtype Concrete = Concrete { isConcrete :: Bool }
    deriving (Eq, Ord, Show, Generic)

instance NFData Concrete

instance Default Concrete where
    def = Concrete False

-- | Kore identifier representing the @concrete@ attribute symbol.
concreteId :: Id Object
concreteId = "concrete"

-- | Kore symbol representing the @concrete@ attribute.
concreteSymbol :: SymbolOrAlias Object
concreteSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = concreteId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @concrete@ attribute.
concreteAttribute :: CommonKorePattern
concreteAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = concreteSymbol
            , applicationChildren = []
            }

instance ParseAttributes Concrete where
    parseAttribute =
        withApplication $ \params args Concrete { isConcrete } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isConcrete failDuplicate
            return Concrete { isConcrete = True }
      where
        withApplication = Parser.withApplication concreteId
        failDuplicate = Parser.failDuplicate concreteId
