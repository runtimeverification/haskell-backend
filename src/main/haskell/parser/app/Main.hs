module Main where

import KoreParser

import qualified Data.ByteString as ByteString
import System.Environment (getArgs)

main :: IO ()
main = do
    (fileName:_) <- getArgs
    contents <- ByteString.readFile fileName
    print (fromKore contents)
