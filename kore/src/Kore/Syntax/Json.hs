{-# LANGUAGE OverloadedStrings #-}

module Kore.Syntax.Json (
    -- API
    JsonError (..),
    encodePattern,
    encodeKoreJson,
    decodePattern,
    decodeKoreJson,
) where

import Data.Aeson as Json
import Data.Aeson.Encode.Pretty as Json
import Data.ByteString.Lazy (ByteString)
import Data.Either.Extra hiding (Left, Right)
import Kore.Attribute.Attributes (ParsedPattern)
import Kore.Syntax qualified as Kore
import Kore.Syntax.Json.Internal
import Kore.Syntax.Variable (VariableName (..))
import Prelude.Kore

-- reading

{- | read text into KorePattern, then check for consistency and
 construct a ParsedPattern
-}
decodePattern :: ByteString -> Either JsonError ParsedPattern
decodePattern bs =
    mapLeft ParseError (decodeKoreJson bs) >>= toParsedPattern

-- | low-level: read text into KorePattern
decodeKoreJson :: ByteString -> Either String KorePattern
decodeKoreJson = Json.eitherDecode'

------------------------------------------------------------
-- writing

-- | Write a Pattern to a json byte string.
encodePattern :: Kore.Pattern VariableName ann -> ByteString
encodePattern = encodeKoreJson . fromPattern

encodeKoreJson :: KorePattern -> ByteString
encodeKoreJson = Json.encodePretty' prettyJsonOpts

prettyJsonOpts :: Json.Config
prettyJsonOpts =
    defConfig
        { confIndent = Spaces 2
        , confCompare =
            keyOrder -- retains the field order in all constructors
                [ "tag"
                , "assoc"
                , "name"
                , "symbol"
                , "sort"
                , "sorts"
                , "var"
                , "varSort"
                , "argSort"
                , "resultSort"
                , "arg"
                , "args"
                , "source"
                , "dest"
                , "value"
                ]
        }
