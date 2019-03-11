{-|
Module      : Kore.Attribute.Simplification
Description : Function simplification axiom attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com


The simplification attribute identifies axioms that are useful for
simplifying configurations, without being part of the main semantics.

Kore syntax: @simplification{}()@

Informal example of an axiom that would use the simplification attribute:

(x +Int y) +Int z = (x +Int z) +Int y
    if concrete(x) and concrete(z) and not concrete(y)
-}
module Kore.Attribute.Simplification
    ( Simplification (..)
    , simplificationId, simplificationSymbol, simplificationAttribute
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

{- | @Simplification@ represents the @simplification@ attribute for axioms.
 -}
newtype Simplification = Simplification { isSimplification :: Bool }
    deriving (Eq, Ord, Show, Generic)

instance NFData Simplification

instance Default Simplification where
    def = Simplification False

-- | Kore identifier representing the @simplification@ attribute symbol.
simplificationId :: Id Object
simplificationId = "simplification"

-- | Kore symbol representing the @simplification@ attribute.
simplificationSymbol :: SymbolOrAlias Object
simplificationSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = simplificationId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @simplification@ attribute.
simplificationAttribute :: CommonKorePattern
simplificationAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = simplificationSymbol
            , applicationChildren = []
            }

instance ParseAttributes Simplification where
    parseAttribute =
        withApplication $ \params args Simplification { isSimplification } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isSimplification failDuplicate
            return Simplification { isSimplification = True }
      where
        withApplication = Parser.withApplication simplificationId
        failDuplicate = Parser.failDuplicate simplificationId
