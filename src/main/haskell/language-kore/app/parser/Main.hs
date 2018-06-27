{-# LANGUAGE NamedFieldPuns #-}

module Main
  ( main
  ) where

import           Data.Semigroup                             ( (<>) )
import           Control.Monad                              ( when )
import           Options.Applicative                        ( Parser
                                                            , InfoMod
                                                            , str
                                                            , help
                                                            , metavar
                                                            , fullDesc
                                                            , progDesc
                                                            , header
                                                            , argument )

import           Data.Kore.Error                            ( printError )
import           Data.Kore.Parser.Parser                    ( fromKore )
import           Data.Kore.AST.Sentence                     ( KoreDefinition )
import           Data.Kore.ASTVerifier.DefinitionVerifier   ( defaultAttributesVerification
                                                            , AttributesVerification(DoNotVerifyAttributes)
                                                            , verifyDefinition )

import           GlobalMain                                 ( MainOptions(..)
                                                            , mainGlobal
                                                            , enableDisableFlag
                                                            , clockSomething
                                                            , clockSomethingIO )

{-
Main module to run kore-parser
TODO: add command line argument tab-completion
-}

-- | Main options record
data KoreParserOptions = KoreParserOptions
    { fileName    :: !String -- ^ Filename to parse and verify
    , willPrint   :: !Bool   -- ^ Option to print definition
    , willVerify  :: !Bool   -- ^ Option to verify definition
    , willChkAttr :: !Bool   -- ^ Option to check attributes during verification
    }

-- | Command Line Argument Parser
commandLineParser :: Parser KoreParserOptions
commandLineParser =
    KoreParserOptions
    <$> argument str
        (  metavar "FILE"
        <> help "Kore source file to parse [and verify]" )
    <*> enableDisableFlag "print"
        True False True
        "printing parsed definition to stdout [default enabled]"
    <*> enableDisableFlag "verify"
        True False True
        "Verify well-formedness of parsed definition [default enabled]"
    <*> enableDisableFlag "chkattr"
        True False True
            "attributes checking during verification [default enabled]"


-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    (  fullDesc
    <> progDesc "Parses Kore definition in FILE; optionally, \
                \Verifies well-formedness"
    <> header "kore-parser - a parser for Kore definitions" )


-- | Parses a kore file and Check wellformedness
main :: IO ()
main = do
  options <- mainGlobal commandLineParser parserInfoModifiers
  case localOptions options of
    Nothing -> return () -- global options parsed, but local failed; exit gracefully
    Just KoreParserOptions
         { fileName
         , willPrint
         , willVerify
         , willChkAttr
         } -> do
      parsedDefinition <- mainParse fileName
      when willVerify $ mainVerify willChkAttr parsedDefinition
      when willPrint  $ print parsedDefinition


-- | IO action that parses a kore definition from a filename and prints timing information.
mainParse :: String -> IO KoreDefinition
mainParse fileName = do
    contents <-
        clockSomethingIO "Reading the input file" (readFile fileName)
    parseResult <-
        clockSomething "Parsing the file" (fromKore fileName contents)
    case parseResult of
        Left err         -> error err
        Right definition -> return definition


-- | IO action verifies well-formedness of Kore definition and prints timing information.
mainVerify
    :: Bool -- ^ whether to check (True) or ignore attributes during verification
    -> KoreDefinition -- ^ Parsed definition to check well-formedness
    -> IO ()
mainVerify willChkAttr definition =
    let attributesVerification =
            if willChkAttr
            then case defaultAttributesVerification of
                   Left err           -> error (printError err)
                   Right verification -> verification
            else DoNotVerifyAttributes
    in do
      verifyResult <- clockSomething
                      "Verifying the definition"
                      ( verifyDefinition
                        attributesVerification
                        definition )
      case verifyResult of
        Left err1 -> error (printError err1)
        Right _   -> return ()
