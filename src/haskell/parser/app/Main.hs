module Main where

import KoreAST
import KoreParser

main :: IO ()
main = parse idParser "" "a"
