{-|
Module      : Kore.Attribute.Label
Description : Sentence label attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Label
    ( Label (..)
    , labelId, labelSymbol, labelAttribute
    ) where

import Control.DeepSeq
       ( NFData )
import Data.Default
import Data.Text
       ( Text )
import GHC.Generics
       ( Generic )

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

-- | @Label@ represents the @overload@ attribute for symbols.
newtype Label = Label { unLabel :: Maybe Text }
    deriving (Generic, Eq, Ord, Show)

instance Semigroup Label where
    (<>) a@(Label (Just _)) _ = a
    (<>) _                  b = b

instance Monoid Label where
    mappend = (<>)
    mempty = Label Nothing

instance Default Label where
    def = mempty

instance NFData Label

-- | Kore identifier representing the @label@ attribute symbol.
labelId :: Id Object
labelId = "label"

-- | Kore symbol representing the @label@ attribute.
labelSymbol :: SymbolOrAlias Object
labelSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = labelId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @overload@ attribute.
labelAttribute
    :: Text
    -> CommonKorePattern
labelAttribute label =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = labelSymbol
            , applicationChildren =
                [ (asCommonKorePattern . StringLiteralPattern)
                    (StringLiteral label)
                ]
            }

instance ParseAttributes Label where
    parseAttribute = withApplication parseApplication
      where
        parseApplication params args Label { unLabel }
          | Just _ <- unLabel = failDuplicate
          | otherwise = do
            Parser.getZeroParams params
            arg1 <- Parser.getOneArgument args
            str <- Parser.getStringLiteral arg1
            return Label { unLabel = Just (getStringLiteral str) }
        withApplication = Parser.withApplication labelId
        failDuplicate = Parser.failDuplicate labelId
