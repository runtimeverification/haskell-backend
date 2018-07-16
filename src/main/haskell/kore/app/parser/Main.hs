{-# LANGUAGE NamedFieldPuns #-}

module Main
  ( main
  ) where

import           Control.Monad                            (when)
import qualified Data.Map                                 as Map
import           Data.Semigroup                           ((<>))
import           Options.Applicative                      (InfoMod, Parser,
                                                           argument, fullDesc,
                                                           header, help, long,
                                                           metavar, progDesc,
                                                           str, strOption,
                                                           value)

import           Data.Kore.AST.Kore                       (CommonKorePattern)
import           Data.Kore.AST.Sentence                   (KoreDefinition,
                                                           ModuleName (..))
import           Data.Kore.ASTPrettyPrint                 (prettyPrintToString)
import           Data.Kore.ASTVerifier.DefinitionVerifier (AttributesVerification (DoNotVerifyAttributes),
                                                           defaultAttributesVerification,
                                                           verifyAndIndexDefinition)
import           Data.Kore.ASTVerifier.PatternVerifier    (verifyStandalonePattern)
import           Data.Kore.Error                          (printError)
import           Data.Kore.IndexedModule.IndexedModule    (KoreIndexedModule)
import           Data.Kore.Parser.Parser                  (fromKore,
                                                           fromKorePattern)

import           GlobalMain                               (MainOptions (..),
                                                           clockSomething,
                                                           clockSomethingIO,
                                                           enableDisableFlag,
                                                           mainGlobal)

{-
Main module to run kore-parser
TODO: add command line argument tab-completion
-}

-- | Main options record
data KoreParserOptions = KoreParserOptions
    { fileName            :: !String
    -- ^ Name for a file containing a definition to parse and verify
    , patternFileName     :: !String
    -- ^ Name for file containing a pattern to parse and verify
    , mainModuleName      :: !String
    -- ^ the name of the main module in the definition
    , willPrintDefinition :: !Bool   -- ^ Option to print definition
    , willPrintPattern    :: !Bool   -- ^ Option to print pattern
    , willVerify          :: !Bool   -- ^ Option to verify definition
    , willChkAttr         :: !Bool   -- ^ Option to check attributes during verification
    }

-- | Command Line Argument Parser
commandLineParser :: Parser KoreParserOptions
commandLineParser =
    KoreParserOptions
    <$> argument str
        (  metavar "FILE"
        <> help "Kore source file to parse [and verify]" )
    <*> strOption
        (  metavar "PATTERN_FILE"
        <> long "pattern"
        <> help "Kore pattern source file to parse [and verify]. Needs --module."
        <> value "" )
    <*> strOption
        (  metavar "MODULE"
        <> long "module"
        <> help "The name of the main module in the Kore definition"
        <> value "" )
    <*> enableDisableFlag "print-definition"
        True False True
        "printing parsed definition to stdout [default enabled]"
    <*> enableDisableFlag "print-pattern"
        True False True
        "printing parsed pattern to stdout [default enabled]"
    <*> enableDisableFlag "verify"
        True False True
        "Verify well-formedness of parsed definition [default enabled]"
    <*> enableDisableFlag "chkattr"
        True False True
            "attributes checking during verification [default enabled]"


-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
    <> progDesc "Parses Kore definition in FILE; optionally, \
                \Verifies well-formedness"
    <> header "kore-parser - a parser for Kore definitions"


-- TODO(virgil): Maybe add a regression test for main.
-- | Parses a kore file and Check wellformedness
main :: IO ()
main = do
  options <- mainGlobal commandLineParser parserInfoModifiers
  case localOptions options of
    Nothing -> return () -- global options parsed, but local failed; exit gracefully
    Just KoreParserOptions
        { fileName
        , patternFileName
        , mainModuleName
        , willPrintDefinition
        , willPrintPattern
        , willVerify
        , willChkAttr
        }
      -> do
        parsedDefinition <- mainDefinitionParse fileName
        indexedModules <- if willVerify
            then mainVerify willChkAttr parsedDefinition
            else return Map.empty
        when willPrintDefinition $
            putStrLn (prettyPrintToString parsedDefinition)

        when (patternFileName /= "") $ do
            parsedPattern <- mainPatternParse patternFileName
            when willVerify $ do
                indexedModule <-
                    mainModule (ModuleName mainModuleName) indexedModules
                mainPatternVerify indexedModule parsedPattern
            when willPrintPattern $
                putStrLn (prettyPrintToString parsedPattern)

mainModule
    :: ModuleName
    -> Map.Map ModuleName KoreIndexedModule
    -> IO KoreIndexedModule
mainModule name modules =
    case Map.lookup name modules of
        Nothing ->
            error
                (  "The main module, '"
                ++ getModuleName name
                ++ "', was not found. Check the --module flag."
                )
        Just m -> return m

-- | IO action that parses a kore definition from a filename and prints timing
-- information.
mainDefinitionParse :: String -> IO KoreDefinition
mainDefinitionParse = mainParse fromKore

-- | IO action that parses a kore pattern from a filename and prints timing
-- information.
mainPatternParse :: String -> IO CommonKorePattern
mainPatternParse = mainParse fromKorePattern

-- | IO action that parses a kore AST entity from a filename and prints timing
-- information.
mainParse
    :: (FilePath -> String -> Either String a)
    -> String
    -> IO a
mainParse parser fileName = do
    contents <-
        clockSomethingIO "Reading the input file" (readFile fileName)
    parseResult <-
        clockSomething "Parsing the file" (parser fileName contents)
    case parseResult of
        Left err         -> error err
        Right definition -> return definition

-- | IO action verifies well-formedness of Kore definition and prints
-- timing information.
mainVerify
    :: Bool -- ^ whether to check (True) or ignore attributes during verification
    -> KoreDefinition -- ^ Parsed definition to check well-formedness
    -> IO (Map.Map ModuleName KoreIndexedModule)
mainVerify willChkAttr definition =
    let attributesVerification =
            if willChkAttr
            then case defaultAttributesVerification of
                   Left err           -> error (printError err)
                   Right verification -> verification
            else DoNotVerifyAttributes
    in do
      verifyResult <-
        clockSomething "Verifying the definition"
            ( verifyAndIndexDefinition attributesVerification definition )
      case verifyResult of
        Left err1            -> error (printError err1)
        Right indexedModules -> return indexedModules


-- | IO action verifies well-formedness of Kore patterns and prints
-- timing information.
mainPatternVerify
    :: KoreIndexedModule
    -- ^ Module containing definitions visible in the pattern
    -> CommonKorePattern -- ^ Parsed pattern to check well-formedness
    -> IO ()
mainPatternVerify indexedModule patt =
    do
      verifyResult <-
        clockSomething "Verifying the pattern"
            ( verifyStandalonePattern indexedModule patt)
      case verifyResult of
        Left err1 -> error (printError err1)
        Right _   -> return ()
