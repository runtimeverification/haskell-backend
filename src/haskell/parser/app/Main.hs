module Main where

import KoreLexeme

import Data.Attoparsec.ByteString.Char8 (parseOnly, endOfInput)
import Data.ByteString.Char8 (pack)

main :: IO ()
main = print (parseOnly (skipWhitespace *> idParser <* endOfInput) (pack " /* * */ //b\na"))
