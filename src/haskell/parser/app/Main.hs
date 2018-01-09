module Main where

import KoreAST
import KoreLexeme
import KoreParser

import Data.Attoparsec.ByteString.Char8
import Data.ByteString.Char8

main :: IO ()
main = print (parseOnly (skipWhitespace *> idParser <* endOfInput) (pack " /* * */ //b\na"))
