{-|
Module      : Kore.Attribute.Functional
Description : Functional symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Functional
    ( Functional (..)
    , functionalId, functionalSymbol, functionalAttribute
    ) where

import qualified Control.Monad as Monad
import           Data.Default

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

{- | @Functional@ represents the @functional@ attribute for symbols.
 -}
newtype Functional = Functional { isDeclaredFunctional :: Bool }
    deriving (Eq, Ord, Show)

instance Semigroup Functional where
    (<>) (Functional a) (Functional b) = Functional (a || b)

instance Monoid Functional where
    mempty = Functional False

instance Default Functional where
    def = mempty

-- | Kore identifier representing the @functional@ attribute symbol.
functionalId :: Id Object
functionalId = "functional"

-- | Kore symbol representing the @functional@ attribute.
functionalSymbol :: SymbolOrAlias Object
functionalSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = functionalId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @functional@ attribute.
functionalAttribute :: CommonKorePattern
functionalAttribute =
    (KoreObjectPattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = functionalSymbol
            , applicationChildren = []
            }

instance ParseAttributes Functional where
    parseAttribute =
        withApplication parseApplication
      where
        parseApplication params args Functional { isDeclaredFunctional } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isDeclaredFunctional failDuplicate
            return Functional { isDeclaredFunctional = True }
        withApplication = Parser.withApplication functionalId
        failDuplicate = Parser.failDuplicate functionalId
