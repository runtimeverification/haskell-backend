module Main (main) where

import Prelude.Kore

import Control.Monad.Catch
    ( Exception (..)
    , SomeException
    , handle
    )
import qualified Data.Map.Strict as Map
import Data.Maybe

import Kore.AST.ApplicativeKore
import Kore.ASTVerifier.DefinitionVerifier
    ( verifyAndIndexDefinition
    )
import Kore.Attribute.Symbol
    ( StepperAttributes
    )
import qualified Kore.Builtin as Builtin
import Kore.Debug
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    , toVerifiedDefinition
    )
import Kore.Log
    ( runLoggerT
    )
import qualified Kore.Log as Log
import Kore.Log.ErrorVerify
    ( errorVerify
    )
import Kore.Options
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
            parseKoreParserOptions
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

            let KoreParserOptions { patternOpt } = koreParserOptions
            for_ patternOpt $ \patternOptions -> do
                let PatternOptions { mainModuleName } = patternOptions
                indexedModule <- if willVerify then Just <$>
                    ( lookupMainModule
                        (ModuleName mainModuleName)
                        indexedModules
                    & lift )
                    else return Nothing
                let PatternOptions { patternFileNames } = patternOptions
                for_ patternFileNames $ \patternFileName -> do
                    parsedPattern <- mainPatternParse patternFileName
                    when willVerify $ do
                        _ <- mainPatternVerify (fromJust indexedModule) parsedPattern
                        return ()
                    let KoreParserOptions { willPrintPattern } =
                            koreParserOptions
                    when willPrintPattern $
                        lift $ putDoc (debug parsedPattern)

-- | IO action that parses a kore definition from a filename and prints timing
-- information.
mainDefinitionParse :: FilePath -> Main ParsedDefinition
mainDefinitionParse = mainParse parseKoreDefinition

-- | IO action that parses a kore pattern from a filename and prints timing
-- information.
mainPatternParse :: FilePath -> Main ParsedPattern
mainPatternParse = mainParse parseKorePattern

-- | IO action verifies well-formedness of Kore definition and prints
-- timing information.
mainVerify
    :: ParsedDefinition
    -- ^ Parsed definition to check well-formedness
    -> IO (Map.Map ModuleName (VerifiedModule StepperAttributes))
mainVerify definition = flip runLoggerT Log.emptyLogger $ do
    verifyResult <-
        clockSomething "Verifying the definition"
            (verifyAndIndexDefinition
                Builtin.koreVerifiers
                definition
            )
    either errorVerify return verifyResult
