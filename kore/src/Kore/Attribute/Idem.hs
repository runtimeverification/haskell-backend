{-|
Module      : Kore.Attribute.Idem
Description : Idempotency axiom attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Idem
    ( Idem (..)
    , idemId, idemSymbol, idemAttribute
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

{- | @Idem@ represents the @idem@ attribute for axioms.
 -}
newtype Idem = Idem { isIdem :: Bool }
    deriving (Eq, Ord, Show, Generic)

instance NFData Idem

instance Default Idem where
    def = Idem False

-- | Kore identifier representing the @idem@ attribute symbol.
idemId :: Id Object
idemId = "idem"

-- | Kore symbol representing the @idem@ attribute.
idemSymbol :: SymbolOrAlias Object
idemSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = idemId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @idem@ attribute.
idemAttribute :: CommonKorePattern
idemAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = idemSymbol
            , applicationChildren = []
            }

instance ParseAttributes Idem where
    parseAttribute =
        withApplication $ \params args Idem { isIdem } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isIdem failDuplicate
            return Idem { isIdem = True }
      where
        withApplication = Parser.withApplication idemId
        failDuplicate = Parser.failDuplicate idemId
