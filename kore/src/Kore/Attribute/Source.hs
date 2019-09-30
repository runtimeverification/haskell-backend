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

import Control.Applicative
    ( many
    )
import Control.DeepSeq
    ( NFData
    )
import Data.Default
import Data.Maybe
import qualified Data.Text as Text
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Text.Megaparsec
    ( Parsec
    , noneOf
    , parseMaybe
    )
import Text.Megaparsec.Char

import Kore.Attribute.Parser as AttributeParser
import Kore.Debug
import qualified Kore.Error

newtype Source = Source
    { unSource :: Maybe String
    } deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic Source

instance SOP.HasDatatypeInfo Source

instance Debug Source

instance Diff Source

instance NFData Source

instance Default Source where
    def = Source Nothing

-- | Kore identifier representing the @location@ attribute symbol.
sourceId :: Id
sourceId = "org'Stop'kframework'Stop'attributes'Stop'Source"

instance ParseAttributes Source where
    parseAttribute = AttributeParser.withApplication sourceId parseApplication
      where

        parseApplication
            :: [Sort]
            -> [AttributePattern]
            -> Source
            -> AttributeParser.Parser Source
        parseApplication params args s@(Source Nothing) = do
            AttributeParser.getZeroParams params
            case args of
                [] -> pure s
                [_] -> do
                    arg <- AttributeParser.getOneArgument args
                    StringLiteral str <- AttributeParser.getStringLiteral arg
                    pure
                        . fromMaybe def
                        . parseMaybe sourceParser
                        $ Text.unpack str
                _ ->
                    Kore.Error.koreFail
                        ("expected one argument, found " ++ show (length args))
        parseApplication _ _ _ =
            AttributeParser.failDuplicate sourceId

    -- TODO (thomas.tuegel): Implement
    toAttributes _ = def

-- | This parser is used to parse the inner representation of the attribute.
-- The expected format is "Source(path)" where path is a FilePath.
type StringParser = Parsec String String

sourceParser :: StringParser Source
sourceParser = Source <$> (Just <$> sourceParser0)
  where
    sourceParser0 :: StringParser String
    sourceParser0 =
        string "Source(" *> many (noneOf excludedChars) <* string ")"

    excludedChars :: String
    excludedChars = ")"
