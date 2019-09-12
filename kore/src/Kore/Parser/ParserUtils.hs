{-# OPTIONS_GHC -fno-warn-orphans #-}
{-|
Module      : Kore.Parser.ParserUtils
Description : Helper tools for parsing Kore. Meant for internal use only.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

Helper tools for parsing Kore. Meant for internal use only.
-}
module Kore.Parser.ParserUtils where

import Control.Applicative
    ( (<|>)
    )
import Control.Monad
    ( void
    )
import Data.Functor
    ( ($>)
    )
import Text.Megaparsec
    ( Parsec
    , anySingle
    , eof
    , lookAhead
    , parse
    , takeWhileP
    )
import qualified Text.Megaparsec.Char as Parser
import Text.Megaparsec.Error
    ( ShowErrorComponent (..)
    , errorBundlePretty
    )

type Parser = Parsec String String

{-|'peekChar' is similar to Attoparsec's 'peekChar'. It returns the next
available character in the input, without consuming it. Returns 'Nothing'
if the input does not have any available characters.
-}
peekChar :: Parser (Maybe Char)
peekChar =
    Just <$> peekChar' <|> return Nothing

{-|'peekChar'' is similar to Attoparsec's 'peekChar''. It returns the next
available character in the input, without consuming it. Fails if the input
does not have any available characters.
-}
peekChar' :: Parser Char
peekChar' =
    lookAhead anySingle

{-|'scan' is similar to Attoparsec's 'scan'. It does the same thing as
'runScanner', but without returning the last state.
-}
scan :: a -> (a -> Char -> Maybe a) -> Parser String
scan state delta = fst <$> runScanner state delta

{-|'runScanner' is similar to Attoparsec's 'runScanner'. It parses a string
with the given state machine, stopping when the state function returns
'Nothing' or at the end of the input (without producing an error).

Returns a pair of the parsed string and the last state.
-}
runScanner :: a -> (a -> Char -> Maybe a) -> Parser (String, a)
runScanner state delta = do
    maybeC <- peekChar
    case maybeC >>= delta state of
        Nothing -> return ("", state)
        Just s -> do
            c <- anySingle
            (reminder, finalState) <- runScanner s delta
            return (c :reminder, finalState)

{-|'skipSpace' is similar to Attoparsec's 'skipSpace'. It consumes all
characters until the first non-space one.  It does not skip comments.
-}
skipSpace :: Parser ()
skipSpace = Parser.space

{-|'takeWhile' is similar to Attoparsec's 'takeWhile'. It consumes all
the input characters that satisfy the given predicate and returns them
as a string.
-}
takeWhile :: (Char -> Bool) -> Parser String
takeWhile = takeWhileP Nothing

{-|'endOfInput' is similar to Attoparsec's 'endOfInput'. It matches only the
end-of-input position.
-}
endOfInput :: Parser ()
endOfInput = eof

instance ShowErrorComponent String where
    showErrorComponent str = str

{-|'parseOnly' is similar to Attoparsec's 'parseOnly'. It takes a parser,
a FilePath that is used for generating error messages and an input string
and produces either a parsed object, or an error message.
-}
parseOnly :: Parser a -> FilePath -> String -> Either String a
parseOnly parser filePathForErrors input =
    case parse parser filePathForErrors input of
        Left err -> Left (errorBundlePretty err)
        Right v  -> Right v

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
    mc <- peekChar
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
        mc <- peekChar
        case mc of
            Nothing -> fail "Unexpected end of input."
            Just c
                | c == endChar ->
                    skipCharParser skipWhitespace endChar $> []
                | otherwise ->
                    (:) <$> itemParser <*> sepByCharWithDelimitingChars'
  where
    sepByCharWithDelimitingChars' = do
        mc <- peekChar
        case mc of
            Nothing -> fail "Unexpected end of input."
            Just c
                | c == endChar ->
                    skipCharParser skipWhitespace endChar $> []
                | c == delimiter ->
                    skipCharParser skipWhitespace delimiter *>
                        ((:) <$> itemParser <*> sepByCharWithDelimitingChars')
                | otherwise -> fail ("Unexpected character: '" ++ c:"'. " ++
                    "Expecting '" ++ delimiter:"' or '" ++ endChar:"'.")
