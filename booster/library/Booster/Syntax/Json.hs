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
    prettyPattern,
) where

import Data.Aeson as Json
import Data.Aeson.Encode.Pretty as Json
import Data.ByteString.Lazy (ByteString)
import Data.Either.Extra hiding (Left, Right)
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text.Internal.Builder qualified as TB
import Data.Text.Lazy qualified as Text (toStrict)

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

-- pretty-printer for kore json (should be upstreamed)

prettyPattern :: KorePattern -> Text
prettyPattern = Text.toStrict . TB.toLazyText . go
  where
    go = \case
        KJEVar{name, sort} ->
            fromId name <> ":" <> prettySort sort
        KJSVar{name, sort} ->
            fromId name <> ":" <> prettySort sort
        KJApp{name, sorts, args} ->
            fromId name
                <> curlies (map prettySort sorts)
                <> parens (map go args)
        KJString{value} ->
            TB.fromString $ show value
        KJTop{sort} ->
            "#Top" <> curlies [prettySort sort]
        KJBottom{sort} ->
            "#Bottom" <> curlies [prettySort sort]
        KJNot{sort, arg} ->
            "#Not" <> curlies [prettySort sort] <> parens [go arg]
        KJAnd{sort, patterns} ->
            "#And" <> curlies [prettySort sort] <> parens (map go patterns)
        KJOr{sort, patterns} ->
            "#Or" <> curlies [prettySort sort] <> parens (map go patterns)
        KJImplies{sort, first, second} ->
            "#Implies" <> curlies [prettySort sort] <> parens [go first, go second]
        KJIff{sort, first, second} ->
            "#Iff" <> curlies [prettySort sort] <> parens [go first, go second]
        KJForall{sort, var, varSort, arg} ->
            "#Forall"
                <> curlies [prettySort sort]
                <> parens [fromId var <> ":" <> prettySort varSort, go arg]
        KJExists{sort, var, varSort, arg} ->
            "#Exists"
                <> curlies [prettySort sort]
                <> parens [fromId var <> ":" <> prettySort varSort, go arg]
        KJMu{var, varSort, arg} ->
            "#Mu"
                <> parens [fromId var <> ":" <> prettySort varSort, go arg]
        KJNu{var, varSort, arg} ->
            "#Nu"
                <> parens [fromId var <> ":" <> prettySort varSort, go arg]
        KJCeil{argSort, sort, arg} ->
            "#Ceil"
                <> curlies (map prettySort [argSort, sort])
                <> parens [go arg]
        KJFloor{argSort, sort, arg} ->
            "#Floor"
                <> curlies (map prettySort [argSort, sort])
                <> parens [go arg]
        KJEquals{argSort, sort, first, second} ->
            "#Equals"
                <> curlies (map prettySort [argSort, sort])
                <> parens (map go [first, second])
        KJIn{argSort, sort, first, second} ->
            "#In"
                <> curlies (map prettySort [argSort, sort])
                <> parens (map go [first, second])
        KJNext{sort, dest} ->
            "#Next" <> curlies [prettySort sort] <> parens [go dest]
        KJRewrites{sort, source, dest} ->
            "#Next" <> curlies [prettySort sort] <> parens (map go [source, dest])
        KJDV{sort, value} ->
            "#DV" <> curlies [prettySort sort] <> parens [TB.fromText value]
        KJMultiOr{sort, argss} ->
            "#Or" <> curlies [prettySort sort] <> parens (map go (NE.toList argss))
        KJLeftAssoc{symbol, sorts, argss} ->
            "#LeftAssoc"
                <> parens (fromId symbol <> curlies (map prettySort sorts) : map go (NE.toList argss))
        KJRightAssoc{symbol, sorts, argss} ->
            "#RightAssoc"
                <> parens (fromId symbol <> curlies (map prettySort sorts) : map go (NE.toList argss))

    prettySort :: Sort -> TB.Builder
    prettySort (SortVar name) = fromId name
    prettySort (SortApp name args) = fromId name <> parens (map prettySort args)

    fromId = TB.fromText . getId

    parens ts = "(" <> commaSep ts <> ")"

    curlies ts = "{" <> commaSep ts <> "}"

    -- intercalate "," variant for a text builder
    commaSep [] = ""
    commaSep [x] = x
    commaSep (x : xs) = x <> TB.singleton ',' <> commaSep xs
