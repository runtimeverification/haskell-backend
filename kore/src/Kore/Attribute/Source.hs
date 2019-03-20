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
                 ( many, optional )
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
import qualified Kore.Attribute.Parser as Parser

data Source = Source
    { unSource :: Maybe String
    } deriving (Eq, Ord, Show, Generic)

instance NFData Source

instance Default Source where
    def = Source Nothing

-- | Kore identifier representing the @location@ attribute symbol.
sourceId :: Id Object
sourceId = "org'Stop'kframework'Stop'attributes'Stop'Source"

instance ParseAttributes Source where
    parseAttribute = Parser.withApplication sourceId parseApplication
      where

        parseApplication
            :: [Sort Object]
            -> [CommonKorePattern]
            -> Source
            -> Parser.Parser Source
        parseApplication params args _ = do
            Parser.getZeroParams params
            case args of
                [_] -> do
                    arg <- Parser.getOneArgument args
                    StringLiteral str <- Parser.getStringLiteral arg
                    pure . maybe def id . parseMaybe sourceParser $ Text.unpack str
                _ -> pure def

type Parser = Parsec String String

sourceParser :: Parser Source
sourceParser = Source <$> optional sourceParser0
  where
    sourceParser0 :: Parser String
    sourceParser0 = string "Source(" *> many (noneOf excludedChars) <* string ")"

    excludedChars :: [Char]
    excludedChars = [')']
