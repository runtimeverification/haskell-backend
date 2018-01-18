{-|
Module      : ParserUtils
Description : Helper tools for parsing Kore. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module ParserUtils where

import           Control.Monad                    (void)
import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser

{-|'manyUntilChar' parses a list of 'a' items.

It uses 'itemParser' to parse 0 or more items until 'endchar'
is encountered at the edge of an item (or at the beginning of the input).

Returns a list of items.

The difference between this and the standard 'many' construct is that this one
returns any errors reported by 'itemParser'
-}
manyUntilChar :: Char -> Parser a -> Parser [a]
manyUntilChar endChar itemParser = do
    mc <- Parser.peekChar
    if mc == Just endChar
      then return []
      else (:) <$> itemParser <*> manyUntilChar endChar itemParser

{-|'skipCharParser' skips the given character, consuming any whitespace after.
-}
skipCharParser :: Parser () -> Char -> Parser ()
skipCharParser skipWhitespace c = do
    void(Parser.char c)
    skipWhitespace

{-|'sepByCharWithDelimitingChars' parses a list of 0 or more 'a' items.

The list must start with 'firstChar' and end with 'endChar'. Items must be
delimited by 'delimiter'. The parser uses 'skipWhitespace' to consume any space
after these.

The difference between this and the standard 'sepBy' construct is that this one
returns any errors reported by 'itemParser'
-}
sepByCharWithDelimitingChars
    :: Parser() -> Char -> Char -> Char -> Parser a -> Parser [a]
sepByCharWithDelimitingChars
    skipWhitespace firstChar endChar delimiter itemParser = do
        skipCharParser skipWhitespace firstChar
        mc <- Parser.peekChar
        case mc of
            Nothing -> fail "Unexpected end of input."
            Just c
                | c == endChar ->
                    skipCharParser skipWhitespace endChar *> return []
                | otherwise ->
                    (:) <$> itemParser <*> sepByCharWithDelimitingChars'
  where
    sepByCharWithDelimitingChars' = do
        mc <- Parser.peekChar
        case mc of
            Nothing -> fail "Unexpected end of input."
            Just c
                | c == endChar ->
                    skipCharParser skipWhitespace endChar *> return []
                | c == delimiter ->
                    skipCharParser skipWhitespace delimiter *>
                        ((:) <$> itemParser <*> sepByCharWithDelimitingChars')
                | otherwise -> fail ("Unexpected character: '" ++ c:"'. " ++
                    "Expecting '" ++ delimiter:"' or '" ++ endChar:"'.")
