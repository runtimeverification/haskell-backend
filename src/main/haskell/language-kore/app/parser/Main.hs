module Main where

import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.Error
import           Data.Kore.Parser.Parser

import           Control.Exception                        (evaluate)
import           Control.Monad                            (when)
import           System.Clock                             (Clock (Monotonic),
                                                           diffTimeSpec,
                                                           getTime)

import           CLIParser                                ( KoreParserOpts(..)
                                                          , cliParse )
clockSomething :: String -> a -> IO a
clockSomething description something =
    clockSomethingIO description (evaluate something)

clockSomethingIO :: String -> IO a -> IO a
clockSomethingIO description something = do
    start <- getTime Monotonic
    x <- something
    end <- getTime Monotonic
    putStrLn (description ++" "++ show (diffTimeSpec end start))
    return x

main :: IO ()
main =
    do {
    ; KoreParserOpts{
            fileName    = fileName
          , willPrint   = willPrint 
          , willVerify  = willVerify
          , willChkAttr = willChkAttr } <- cliParse
    ; contents <-
        clockSomethingIO "Reading the input file" (readFile fileName)
    ; parseResult <-
        clockSomething "Parsing the file" (fromKore fileName contents)
    ; let parsedDefinition =
              case parseResult of
                Left err         -> error err
                Right definition -> definition
    ; when (willVerify) (verifyMain willChkAttr parsedDefinition)
    ; when (willPrint) (print parsedDefinition)
    }

verifyMain willChkAttr definition =
    let
        attributesVerification =
            if willChkAttr
            then case defaultAttributesVerification of
                   Left err           -> error (printError err)
                   Right verification -> verification
            else DoNotVerifyAttributes
    in do { verifyResult <-
                clockSomething "Verifying the definition"
                                   ( verifyDefinition
                                     attributesVerification
                                     definition )
          ; case verifyResult of
                 Left err1 -> error (printError err1)
                 Right _   -> return ()
          }
