{-|
Module      : Kore.Attribute.Constructor
Description : Constructor symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Constructor
    ( Constructor (..)
    , constructorId, constructorSymbol, constructorAttribute
    ) where

import qualified Control.Monad as Monad

import Kore.Attribute.Parser as Parser

-- | @Constructor@ represents the @constructor@ attribute for symbols.
newtype Constructor = Constructor { isConstructor :: Bool }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Constructor where
    (<>) (Constructor a) (Constructor b) = Constructor (a || b)

instance Monoid Constructor where
    mempty = Constructor False

instance Default Constructor where
    def = mempty

instance NFData Constructor

-- | Kore identifier representing the @constructor@ attribute symbol.
constructorId :: Id
constructorId = "constructor"

-- | Kore symbol representing the @constructor@ attribute.
constructorSymbol :: SymbolOrAlias
constructorSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = constructorId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @constructor@ attribute.
constructorAttribute :: AttributePattern
constructorAttribute = attributePattern_ constructorSymbol

instance ParseAttributes Constructor where
    parseAttribute = withApplication' parseApplication
      where
        parseApplication params args Constructor { isConstructor } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isConstructor failDuplicate'
            return Constructor { isConstructor = True }
        withApplication' = Parser.withApplication constructorId
        failDuplicate' = Parser.failDuplicate constructorId
