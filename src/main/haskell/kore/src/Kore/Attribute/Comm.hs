{-|
Module      : Kore.Attribute.Comm
Description : Commutativity axiom attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Comm
    ( Comm (..)
    , commId, commSymbol, commAttribute
    ) where

import qualified Control.Monad as Monad
import           Data.Default

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

{- | @Comm@ represents the @comm@ attribute for axioms.
 -}
newtype Comm = Comm { isComm :: Bool }
    deriving (Eq, Ord, Show)

instance Default Comm where
    def = Comm False

-- | Kore identifier representing the @comm@ attribute symbol.
commId :: Id Object
commId = "comm"

-- | Kore symbol representing the @comm@ attribute.
commSymbol :: SymbolOrAlias Object
commSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = commId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @comm@ attribute.
commAttribute :: CommonKorePattern
commAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = commSymbol
            , applicationChildren = []
            }

instance ParseAttributes Comm where
    parseAttribute =
        withApplication $ \params args Comm { isComm } -> do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isComm failDuplicate
            return Comm { isComm = True }
      where
        withApplication = Parser.withApplication commId
        failDuplicate = Parser.failDuplicate commId
