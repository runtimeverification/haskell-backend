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

import Data.Attoparsec.ByteString.Char8 (parseOnly, endOfInput)
import qualified Data.ByteString as ByteString
import System.Environment (getArgs)

main :: IO ()
main = do
    (fileName:_) <- getArgs
    contents <- ByteString.readFile fileName
    print (parseOnly (skipWhitespace *> definitionParser <* endOfInput) contents)
@
-}
module KoreParser ( Definition
                  , definitionParser
                  , fromKore
                  , skipWhitespace
                  ) where

import           KoreAST (Definition)
import           KoreParserImpl (definitionParser)
import           KoreLexeme (skipWhitespace)

import           Data.Attoparsec.ByteString.Char8 (parseOnly, endOfInput)
import qualified Data.ByteString as ByteString

fromKore :: ByteString.ByteString -> Either String Definition
fromKore = parseOnly (skipWhitespace *> definitionParser <* endOfInput)