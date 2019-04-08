{-|
Module      : Kore.Attribute.Axiom.Constructor
Description : Constructor axiom attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

-}
module Kore.Attribute.Axiom.Constructor
    ( Constructor (..)
    , constructorId, constructorSymbol, constructorAttribute
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

{- | @Constructor@ represents the @constructor@ attribute for axioms.
 -}
newtype Constructor = Constructor { isConstructor :: Bool }
    deriving (Eq, Ord, Show, Generic)

instance NFData Constructor

instance Default Constructor where
    def = Constructor False

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
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = constructorSymbol
            , applicationChildren = []
            }

instance ParseAttributes Constructor where
    parseAttribute =
        withApplication $ \params args Constructor { isConstructor } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isConstructor failDuplicate
            return Constructor { isConstructor = True }
      where
        withApplication = Parser.withApplication constructorId
        failDuplicate = Parser.failDuplicate constructorId
