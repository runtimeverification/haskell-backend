{-|
Module      : Kore.Attribute.Function
Description : Function symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Function
    ( Function (..)
    , functionId, functionSymbol, functionAttribute
    ) where

import           Control.DeepSeq
                 ( NFData )
import qualified Control.Monad as Monad
import           Data.Default
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

-- | @Function@ represents the @function@ attribute for symbols.
newtype Function = Function { isDeclaredFunction :: Bool }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Function where
    (<>) (Function a) (Function b) = Function (a || b)

instance Monoid Function where
    mempty = Function False

instance Default Function where
    def = mempty

instance NFData Function

-- | Kore identifier representing the @function@ attribute symbol.
functionId :: Id Object
functionId = "function"

-- | Kore symbol representing the @function@ attribute.
functionSymbol :: SymbolOrAlias Object
functionSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = functionId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @function@ attribute.
functionAttribute :: CommonKorePattern
functionAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = functionSymbol
            , applicationChildren = []
            }

instance ParseAttributes Function where
    parseAttribute =
        withApplication parseApplication
      where
        parseApplication params args Function { isDeclaredFunction } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isDeclaredFunction failDuplicate
            return Function { isDeclaredFunction = True }
        withApplication = Parser.withApplication functionId
        failDuplicate = Parser.failDuplicate functionId
