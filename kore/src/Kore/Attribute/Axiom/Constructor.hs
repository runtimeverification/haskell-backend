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

import qualified Control.Monad as Monad
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Parser as Parser
import Kore.Debug

{- | @Constructor@ represents the @constructor@ attribute for axioms.
 -}
newtype Constructor = Constructor { isConstructor :: Bool }
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Constructor

instance SOP.HasDatatypeInfo Constructor

instance Debug Constructor

instance Diff Constructor

instance NFData Constructor

instance Default Constructor where
    def = Constructor False

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
    parseAttribute =
        withApplication' $ \params args Constructor { isConstructor } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isConstructor failDuplicate'
            return Constructor { isConstructor = True }
      where
        withApplication' = Parser.withApplication constructorId
        failDuplicate' = Parser.failDuplicate constructorId

    toAttributes Constructor { isConstructor } =
        Attributes [constructorAttribute | isConstructor]
