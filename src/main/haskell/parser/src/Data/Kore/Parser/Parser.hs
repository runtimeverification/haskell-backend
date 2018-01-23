{-|
Module      : Data.Kore.Parser.Parser
Description : Parser for the Kore language
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

This is a parser for the Kore language. Sample usage:

@
import Data.Kore.Parser.KoreParser

import           Data.Attoparsec.ByteString.Char8 (parseOnly)
import qualified Data.ByteString as ByteString
import           System.Environment (getArgs)

main :: IO ()
main = do
    (fileName:_) <- getArgs
    contents <- ByteString.readFile fileName
    print (fromKore contents)
    -- or --
    print (parseOnly koreParser contents)
@

-}
module Data.Kore.Parser.Parser ( Definition
                               , fromKore
                               , koreParser
                               ) where

import           Data.Kore.AST                    (Definition)
import           Data.Kore.Parser.Lexeme          (skipWhitespace)
import           Data.Kore.Parser.ParserImpl      (definitionParser)

import           Data.Attoparsec.ByteString.Char8 (Parser, endOfInput,
                                                   parseOnly)
import qualified Data.ByteString                  as ByteString

{-|'koreParser' is a parser for Kore.

The input must contain a full valid Kore defininition and nothing else.
-}
koreParser :: Parser Definition
koreParser = skipWhitespace *> definitionParser <* endOfInput

{-|'fromKore' takes a string repredentation of a Kore Definition and returns
a 'Definition' or a parse error.

The input must contain a full valid Kore defininition and nothing else.
-}
fromKore :: ByteString.ByteString -> Either String Definition
fromKore = parseOnly koreParser
