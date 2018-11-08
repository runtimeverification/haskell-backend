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
import           Data.Default

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

-- | @Constructor@ represents the @constructor@ attribute for symbols.
newtype Constructor = Constructor { isConstructor :: Bool }
    deriving (Eq, Ord, Show)

instance Semigroup Constructor where
    (<>) (Constructor a) (Constructor b) = Constructor (a || b)

instance Monoid Constructor where
    mempty = Constructor False

instance Default Constructor where
    def = mempty

-- | Kore identifier representing the @constructor@ attribute symbol.
constructorId :: Id Object
constructorId = "constructor"

-- | Kore symbol representing the @constructor@ attribute.
constructorSymbol :: SymbolOrAlias Object
constructorSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = constructorId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @constructor@ attribute.
constructorAttribute :: CommonKorePattern
constructorAttribute =
    (KoreObjectPattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = constructorSymbol
            , applicationChildren = []
            }

instance ParseAttributes Constructor where
    parseAttribute = withApplication parseApplication
      where
        parseApplication params args Constructor { isConstructor } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isConstructor failDuplicate
            return Constructor { isConstructor = True }
        withApplication = Parser.withApplication constructorId
        failDuplicate = Parser.failDuplicate constructorId
