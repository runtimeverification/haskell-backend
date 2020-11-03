module Main (main) where

import Prelude.Kore

import Control.Monad.Catch
    ( Exception (..)
    , SomeException
    , handle
    )
import qualified Data.Map.Strict as Map
import Data.Text
    ( Text
    )
import Options.Applicative
    ( InfoMod
    , Parser
    , argument
    , fullDesc
    , header
    , help
    , long
    , metavar
    , progDesc
    , str
    , strOption
    , value
    )

import Kore.AST.ApplicativeKore
import Kore.ASTVerifier.DefinitionVerifier
    ( verifyAndIndexDefinition
    )
import Kore.Attribute.Symbol
    ( StepperAttributes
    )
import qualified Kore.Builtin as Builtin
import Kore.Debug
import Kore.Error
    ( printError
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    , toVerifiedDefinition
    )
import Kore.Log
    ( runLoggerT
    )
import qualified Kore.Log as Log
import Kore.Parser
    ( parseKoreDefinition
    , parseKorePattern
    )
import Kore.Syntax.Definition
import Kore.Unparser as Unparser
import Pretty
    ( putDoc
    )

import System.Exit

import GlobalMain

{-
Main module to run kore-parser
TODO: add command line argument tab-completion
-}

-- | Main options record
data KoreParserOptions = KoreParserOptions
    { fileName            :: !FilePath
    -- ^ Name for a file containing a definition to parse and verify
    , patternFileName     :: !FilePath
    -- ^ Name for file containing a pattern to parse and verify
    , mainModuleName      :: !Text
    -- ^ the name of the main module in the definition
    , willPrintDefinition :: !Bool
    -- ^ Option to print definition
    , willPrintPattern    :: !Bool
    -- ^ Option to print pattern
    , willVerify          :: !Bool
    -- ^ Option to verify definition
    , appKore             :: !Bool
    -- ^ Option to print in applicative Kore syntax
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
        <> help
            "Kore pattern source file to parse [and verify]. Needs --module."
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
    <*> enableDisableFlag "appkore"
        True False False
        (  "printing parsed definition in applicative Kore syntax "
        ++ "[default disabled]"
        )

-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
    <> progDesc "Parses Kore definition in FILE; optionally, \
                \Verifies well-formedness"
    <> header "kore-parser - a parser for Kore definitions"

{- | Top-level exception handler.

Renders exceptions for the user with 'displayException' and exits
unsuccessfully.

 -}
handleTop :: IO () -> IO ()
handleTop =
    handle handler
  where
    handler = die . displayException @SomeException

-- TODO(virgil): Maybe add a regression test for main.
-- | Parses a kore file and Check wellformedness
main :: IO ()
main = handleTop $ do
    options <-
        mainGlobal
            (ExeName "kore-parser")
            Nothing  -- environment variable name for extra arguments
            commandLineParser
            parserInfoModifiers
    for_ (localOptions options) $ \koreParserOptions ->
        flip runLoggerT Log.emptyLogger $ do
            let KoreParserOptions { fileName } = koreParserOptions
            parsedDefinition <- mainDefinitionParse fileName
            let KoreParserOptions { willVerify } = koreParserOptions
            indexedModules <- if willVerify
                then lift $ mainVerify parsedDefinition
                else return Map.empty
            let KoreParserOptions { willPrintDefinition } = koreParserOptions
            let KoreParserOptions { appKore } = koreParserOptions
            lift $ when willPrintDefinition
                $ if appKore
                    then putStrLn
                        $ unparseToString2
                        $ completeDefinition
                        $ toVerifiedDefinition indexedModules
                else putDoc (debug parsedDefinition)

            let KoreParserOptions { patternFileName } = koreParserOptions
            unless (null patternFileName) $ do
                parsedPattern <- mainPatternParse patternFileName
                when willVerify $ do
                    let KoreParserOptions { mainModuleName } = koreParserOptions
                    indexedModule <-
                        lookupMainModule
                            (ModuleName mainModuleName)
                            indexedModules
                        & lift
                    _ <- mainPatternVerify indexedModule parsedPattern
                    return ()
                let KoreParserOptions { willPrintPattern } = koreParserOptions
                when willPrintPattern $
                    lift $ putDoc (debug parsedPattern)

-- | IO action that parses a kore definition from a filename and prints timing
-- information.
mainDefinitionParse :: String -> Main ParsedDefinition
mainDefinitionParse = mainParse parseKoreDefinition

-- | IO action that parses a kore pattern from a filename and prints timing
-- information.
mainPatternParse :: String -> Main ParsedPattern
mainPatternParse = mainParse parseKorePattern

-- | IO action verifies well-formedness of Kore definition and prints
-- timing information.
mainVerify
    :: ParsedDefinition
    -- ^ Parsed definition to check well-formedness
    -> IO
        (Map.Map
            ModuleName
            (VerifiedModule StepperAttributes)
        )
mainVerify definition = flip runLoggerT Log.emptyLogger $ do
    verifyResult <-
        clockSomething "Verifying the definition"
            (verifyAndIndexDefinition
                Builtin.koreVerifiers
                definition
            )
    case verifyResult of
        Left err1            -> liftIO $ die $ printError err1
        Right indexedModules -> return indexedModules
