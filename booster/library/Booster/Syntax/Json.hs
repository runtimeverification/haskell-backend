{- |
Copyright   : (c) Runtime Verification, 2019-2022
License     : BSD-3-Clause
-}
module Booster.Syntax.Json (
    -- API
    KoreJson (..),
    KorePattern,
    JsonParseError,
    addHeader,
    encodeKoreJson,
    decodePattern,
    decodeKoreJson,
    prettyJsonOpts,
    sortOfJson,
) where

import Data.Aeson as Json
import Data.Aeson.Encode.Pretty as Json
import Data.ByteString.Lazy (ByteString)
import Data.Either.Extra hiding (Left, Right)

import Kore.Syntax.Json.Types

-- reading

-- | read text into KorePattern
decodePattern :: ByteString -> Either JsonParseError KorePattern
decodePattern bs =
    term <$> mapLeft JsonParseError (decodeKoreJson bs)

-- | low-level: read text into KorePattern (wrapped in KoreJson)
decodeKoreJson :: ByteString -> Either String KoreJson
decodeKoreJson = Json.eitherDecode'

-- | Errors relating to the json codec
newtype JsonParseError
    = JsonParseError String
    deriving stock (Eq, Show)

------------------------------------------------------------
-- writing

addHeader :: KorePattern -> KoreJson
addHeader = KoreJson KORE KJ1

encodeKoreJson :: KoreJson -> ByteString
encodeKoreJson = Json.encodePretty' prettyJsonOpts

prettyJsonOpts :: Json.Config
prettyJsonOpts =
    defConfig
        { confIndent = Spaces 2
        , confCompare =
            keyOrder -- retains the field order in all constructors
                [ "format"
                , "version"
                , "term"
                , "tag"
                , "assoc"
                , "name"
                , "symbol"
                , "argSort"
                , "sort"
                , "sorts"
                , "var"
                , "varSort"
                , "arg"
                , "args"
                , "argss"
                , "source"
                , "dest"
                , "value"
                ]
        }

sortOfJson :: KorePattern -> Maybe Sort
sortOfJson = \case
    KJEVar{sort} -> Just sort
    KJSVar{sort} -> Just sort
    KJApp{} -> Nothing
    KJString{} -> Just $ SortApp (Id "SortString") []
    KJTop{sort} -> Just sort
    KJBottom{sort} -> Just sort
    KJNot{sort} -> Just sort
    KJAnd{sort} -> Just sort
    KJOr{sort} -> Just sort
    KJImplies{sort} -> Just sort
    KJIff{sort} -> Just sort
    KJForall{sort} -> Just sort
    KJExists{sort} -> Just sort
    KJMu{varSort} -> Just varSort
    KJNu{varSort} -> Just varSort
    KJCeil{sort} -> Just sort
    KJFloor{sort} -> Just sort
    KJEquals{sort} -> Just sort
    KJIn{sort} -> Just sort
    KJNext{sort} -> Just sort
    KJRewrites{sort} -> Just sort
    KJDV{sort} -> Just sort
    KJMultiOr{sort} -> Just sort
    KJLeftAssoc{} -> Nothing
    KJRightAssoc{} -> Nothing
