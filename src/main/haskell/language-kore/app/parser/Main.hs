module Main where

import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.Parser.Parser

import qualified Data.ByteString                          as ByteString
import           System.Environment                       (getArgs)

main :: IO ()
main = do
    (fileName:_) <- getArgs
    contents <- ByteString.readFile fileName
    case fromKore contents of
        Left err -> print err
        Right definition ->
            case verifyDefinition definition of
                Left err1 -> print err1
                Right _   -> print definition
