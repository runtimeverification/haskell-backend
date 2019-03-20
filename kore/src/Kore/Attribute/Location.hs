{-|
Module      : Kore.Attribute.Location
Description : Line/column location attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com

-}
module Kore.Attribute.Location
    ( Location (..)
    , LineColumn (..)
    ) where

import           Control.Applicative
                 ( optional )
import           Control.DeepSeq
                 ( NFData )
import           Data.Default
import qualified Data.Text as Text
import           GHC.Generics
                 ( Generic )
import           Text.Megaparsec
                 ( Parsec, parseMaybe )
import           Text.Megaparsec.Char
import           Text.Megaparsec.Char.Lexer
                 ( decimal )

import           Kore.AST.Kore
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Parser

data LineColumn = LineColumn
    { line   :: Int
    , column :: Int
    } deriving (Eq, Ord, Show, Generic)

instance NFData LineColumn

instance Default LineColumn where
    def = LineColumn 0 0

data Location = Location
    { start :: Maybe LineColumn
    , end   :: Maybe LineColumn
    } deriving (Eq, Ord, Show, Generic)

instance NFData Location

instance Default Location where
    def = Location Nothing Nothing

-- | Kore identifier representing the @location@ attribute symbol.
locationId :: Id Object
locationId = "org'Stop'kframework'Stop'attributes'Stop'Location"

instance ParseAttributes Location where
    parseAttribute = Parser.withApplication locationId parseApplication
      where

        parseApplication
            :: [Sort Object]
            -> [CommonKorePattern]
            -> Location
            -> Parser.Parser Location
        parseApplication params args _ = do
            Parser.getZeroParams params
            case args of
                [_] -> do
                    arg <- Parser.getOneArgument args
                    StringLiteral str <- Parser.getStringLiteral arg
                    pure . maybe def id . parseMaybe locationParser $ Text.unpack str
                _ -> pure def

type Parser = Parsec String String

locationParser :: Parser Location
locationParser =
    Location
        <$> optional parseStart
        <*> optional parseEnd
  where
    parseStart :: Parser LineColumn
    parseStart =
        LineColumn
            <$> (string "Location(" *> decimal)
            <*> (string "," *> decimal)

    parseEnd :: Parser LineColumn
    parseEnd =
        LineColumn
            <$> (string "," *> decimal)
            <*> (string "," *> decimal <* ")")
