module Main where

import KoreParser

import Data.Attoparsec.ByteString.Char8 (parseOnly, endOfInput)
import qualified Data.ByteString as ByteString
import System.Environment (getArgs)

main :: IO ()
main = do
    (fileName:_) <- getArgs
    contents <- ByteString.readFile fileName
    print (parseOnly (skipWhitespace *> definitionParser <* endOfInput) contents)
