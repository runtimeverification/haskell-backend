{-|
Module      : Kore.Attribute.Exit
Description : Exit symbol attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Exit
    ( Exit (..)
    , exitId, exitSymbol, exitAttribute
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

-- | @Exit@ represents the @exit@ attribute for symbols.
newtype Exit = Exit { isDeclaredExit :: Bool }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Exit where
    (<>) (Exit a) (Exit b) = Exit (a || b)

instance Monoid Exit where
    mempty = Exit False

instance Default Exit where
    def = mempty

instance NFData Exit

-- | Kore identifier representing the @exit@ attribute symbol.
exitId :: Id Object
exitId = "exit"

-- | Kore symbol representing the @exit@ attribute.
exitSymbol :: SymbolOrAlias Object
exitSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = exitId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @exit@ attribute.
exitAttribute :: CommonKorePattern
exitAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = exitSymbol
            , applicationChildren = []
            }

instance ParseAttributes Exit where
    parseAttribute =
        withApplication parseApplication
      where
        parseApplication params args Exit { isDeclaredExit } = do
            Parser.getZeroParams params
            Parser.getZeroArguments args
            Monad.when isDeclaredExit failDuplicate
            return Exit { isDeclaredExit = True }
        withApplication = Parser.withApplication exitId
        failDuplicate = Parser.failDuplicate exitId
