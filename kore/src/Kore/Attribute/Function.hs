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

import qualified Control.Monad as Monad
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

-- | @Function@ represents the @function@ attribute for symbols.
newtype Function = Function { isDeclaredFunction :: Bool }
    deriving (GHC.Generic, Eq, Ord, Show)

instance Semigroup Function where
    (<>) (Function a) (Function b) = Function (a || b)

instance Monoid Function where
    mempty = Function False

instance Default Function where
    def = mempty

instance NFData Function

instance SOP.Generic Function

instance SOP.HasDatatypeInfo Function

instance Debug Function

instance Diff Function

-- | Kore identifier representing the @function@ attribute symbol.
functionId :: Id
functionId = "function"

-- | Kore symbol representing the @function@ attribute.
functionSymbol :: SymbolOrAlias
functionSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = functionId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @function@ attribute.
functionAttribute :: AttributePattern
functionAttribute = attributePattern_ functionSymbol

instance ParseAttributes Function where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Function { isDeclaredFunction } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isDeclaredFunction failDuplicate'
            return Function { isDeclaredFunction = True }
        withApplication' = Parser.withApplication functionId
        failDuplicate' = Parser.failDuplicate functionId

    toAttributes Function { isDeclaredFunction } =
        Attributes [functionAttribute | isDeclaredFunction]
