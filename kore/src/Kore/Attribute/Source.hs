{-|
Module      : Kore.Attribute.Source
Description : Source file attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com

-}
module Kore.Attribute.Source
    ( Source (..)
    ) where

import           Control.Applicative
                 ( many )
import           Control.DeepSeq
                 ( NFData )
import           Data.Default
import qualified Data.Text as Text
import           GHC.Generics
                 ( Generic )
import           Text.Megaparsec
                 ( Parsec, noneOf, parseMaybe )
import           Text.Megaparsec.Char

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as AttributeParser

newtype Source = Source
    { unSource :: Maybe String
    } deriving (Eq, Ord, Show, Generic)

instance NFData Source

instance Default Source where
    def = Source Nothing

-- | Kore identifier representing the @location@ attribute symbol.
sourceId :: Id Object
sourceId = "org'Stop'kframework'Stop'attributes'Stop'Source"

instance ParseAttributes Source where
    parseAttribute = AttributeParser.withApplication sourceId parseApplication
      where

        parseApplication
            :: [Sort Object]
            -> [CommonKorePattern]
            -> Source
            -> AttributeParser.Parser Source
        parseApplication params args _ = do
            AttributeParser.getZeroParams params
            case args of
                [_] -> do
                    arg <- AttributeParser.getOneArgument args
                    StringLiteral str <- AttributeParser.getStringLiteral arg
                    pure
                        . maybe def id
                        . parseMaybe sourceParser
                        $ Text.unpack str
                _ -> pure def

-- | This parser is used to parse the inner representation of the attribute.
-- The expected format is "Source(path)" where path is a FilePath.
type StringParser = Parsec String String

sourceParser :: StringParser Source
sourceParser = Source <$> (Just <$> sourceParser0)
  where
    sourceParser0 :: StringParser String
    sourceParser0 = string "Source(" *> many (noneOf excludedChars) <* string ")"

    excludedChars :: String
    excludedChars = ")"
