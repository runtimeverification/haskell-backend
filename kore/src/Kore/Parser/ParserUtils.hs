{- |
Module      : Kore.Parser.ParserUtils
Description : Helper tools for parsing Kore. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Helper tools for parsing Kore. Meant for internal use only.
-}
module Kore.Parser.ParserUtils (
    Parser,
    parseOnly,
    peekChar,
    peekChar',
    readPositiveIntegral,
) where

import Data.Text (
    Text,
 )
import Data.Void (
    Void,
 )
import Options.Applicative (
    auto,
    readerError,
 )
import qualified Options.Applicative.Types as Options
import Prelude.Kore hiding (
    takeWhile,
 )
import Text.Megaparsec (
    Parsec,
    anySingle,
    lookAhead,
    parse,
 )
import Text.Megaparsec.Error (
    errorBundlePretty,
 )

type Parser = Parsec Void Text

{- |'peekChar' is similar to Attoparsec's 'peekChar'. It returns the next
available character in the input, without consuming it. Returns 'Nothing'
if the input does not have any available characters.
-}
peekChar :: Parser (Maybe Char)
peekChar =
    Just <$> peekChar' <|> return Nothing

{- |'peekChar'' is similar to Attoparsec's 'peekChar''. It returns the next
available character in the input, without consuming it. Fails if the input
does not have any available characters.
-}
peekChar' :: Parser Char
peekChar' = lookAhead anySingle

{- |'parseOnly' is similar to Attoparsec's 'parseOnly'. It takes a parser,
a FilePath that is used for generating error messages and an input string
and produces either a parsed object, or an error message.
-}
parseOnly :: Parser a -> FilePath -> Text -> Either String a
parseOnly parser filePathForErrors input =
    case parse parser filePathForErrors input of
        Left err -> Left (errorBundlePretty err)
        Right v -> Right v

readPositiveIntegral ::
    (Read t, Integral t) =>
    (t -> b) ->
    String ->
    Options.ReadM b
readPositiveIntegral ctor optionName = do
    readInt <- auto
    when (readInt <= 0) err
    return . ctor $ readInt
  where
    err = readerError . unwords $ [optionName, "must be a positive integer."]
