{-|
Module      : Data.Kore.Parser.ParserUtils
Description : Helper tools for parsing Kore. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Helper tools for parsing Kore. Meant for internal use only.
-}
module Data.Kore.Parser.ParserUtils where

import           Control.Monad                    (void)
import           Data.Attoparsec.ByteString.Char8 (Parser)
import qualified Data.Attoparsec.ByteString.Char8 as Parser

{-|'manyUntilChar' parses a list of 'a' items.

It uses the item parser to parse 0 or more items until the end character
is encountered at the edge of an item (or at the beginning of the input).

Returns a list of items.

The difference between this and the standard 'many' construct is that this one
returns any errors reported by the item parser.
-}
manyUntilChar :: Char       -- ^ The end character
              -> Parser a   -- ^ The item parser
              -> Parser [a]
manyUntilChar endChar itemParser = do
    mc <- Parser.peekChar
    if mc == Just endChar
      then return []
      else (:) <$> itemParser <*> manyUntilChar endChar itemParser

{-|'skipCharParser' skips the given character, using the provided parser to
consume whatever is after the character.
-}
skipCharParser :: Parser () -> Char -> Parser ()
skipCharParser skipWhitespace c = do
    void(Parser.char c)
    skipWhitespace

{-|'sepByCharWithDelimitingChars' parses a list of 0 or more 'a' items.

The list must start with the start character and end with the end character.
The separator character should occur between items. The parser uses
the skipping parser to consume input after these.

The difference between this and the standard 'sepBy' construct is that this one
returns any errors reported by 'itemParser'
-}
sepByCharWithDelimitingChars
    :: Parser()   -- ^ Skipping parser
    -> Char       -- ^ The start character
    -> Char       -- ^ The end character
    -> Char       -- ^ The separator character
    -> Parser a   -- ^ The item perser
    -> Parser [a]
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
