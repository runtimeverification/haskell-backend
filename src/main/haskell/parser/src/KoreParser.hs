{-|
Module      : KoreParser
Description : Parser for the Kore language
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX

This is a parser for the Kore language. Sample usage:

@
import KoreParser

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
module KoreParser ( Definition
                  , fromKore
                  , koreParser
                  ) where

import           KoreAST (Definition)
import           KoreParserImpl (definitionParser)
import           KoreLexeme (skipWhitespace)

import           Data.Attoparsec.ByteString.Char8 ( parseOnly
                                                  , Parser
                                                  , endOfInput)
import qualified Data.ByteString as ByteString

koreParser :: Parser Definition
koreParser = skipWhitespace *> definitionParser <* endOfInput

fromKore :: ByteString.ByteString -> Either String Definition
fromKore = parseOnly koreParser