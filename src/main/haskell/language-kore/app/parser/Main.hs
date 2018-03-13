module Main where

import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.Parser.Parser

import           System.Environment                       (getArgs)

main :: IO ()
main = do
    (fileName:_) <- getArgs
    contents <- readFile fileName
    case fromKore fileName contents of
        Left err -> print err
        Right definition ->
            case verifyDefinition definition of
                Left err1 -> print err1
                Right _   -> print definition
