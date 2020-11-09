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

module Kore.Parser.ParserUtils
    ( Parser
    , parseOnly
    , endOfInput
    , peekChar
    , peekChar'
    ) where

import Prelude.Kore hiding
    ( takeWhile
    )

import Data.Void
    ( Void
    )
import Text.Megaparsec
    ( Parsec
    , anySingle
    , eof
    , lookAhead
    , parse
    )
import Text.Megaparsec.Error
    ( errorBundlePretty
    )

type Parser = Parsec Void String

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
peekChar' = lookAhead anySingle

{-|'endOfInput' is similar to Attoparsec's 'endOfInput'. It matches only the
end-of-input position.
-}
endOfInput :: Parser ()
endOfInput = eof

{-|'parseOnly' is similar to Attoparsec's 'parseOnly'. It takes a parser,
a FilePath that is used for generating error messages and an input string
and produces either a parsed object, or an error message.
-}
parseOnly :: Parser a -> FilePath -> String -> Either String a
parseOnly parser filePathForErrors input =
    case parse parser filePathForErrors input of
        Left err -> Left (errorBundlePretty err)
        Right v  -> Right v
