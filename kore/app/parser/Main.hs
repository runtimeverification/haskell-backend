module Main (main) where

import Control.Monad.Catch (
    Exception (..),
    SomeException,
    handle,
 )
import qualified Data.Map.Strict as Map
import GlobalMain
import Kore.AST.ApplicativeKore
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Builtin as Builtin
import Kore.Debug
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
    toVerifiedDefinition,
 )
import Kore.Log (
    runLoggerT,
 )
import qualified Kore.Log as Log
import Kore.Log.ErrorVerify (
    errorVerify,
 )
import Kore.Options
import Kore.Parser (
    parseKoreDefinition,
    parseKorePattern,
 )
import Kore.Syntax.Definition
import Kore.Unparser as Unparser
import Kore.Validate.DefinitionVerifier (
    verifyAndIndexDefinition,
 )
import qualified Kore.Validate.PatternVerifier as PatternVerifier
import Prelude.Kore
import Pretty (
    putDoc,
 )
import System.Exit

{-
Main module to run kore-parser
TODO: add command line argument tab-completion
-}

-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> progDesc
            "Parses Kore definition in FILE; optionally, \
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
            Nothing -- environment variable name for extra arguments
            parseKoreParserOptions
            parserInfoModifiers
    for_ (localOptions options) $ \koreParserOptions -> runEmptyLogger $ do
        indexedModules <- do
            let KoreParserOptions{fileName} = koreParserOptions
            parsedDefinition <- mainDefinitionParse fileName
            let KoreParserOptions{willVerify} = koreParserOptions
            indexedModules <-
                if willVerify
                    then fmap Just . lift $ mainVerify parsedDefinition
                    else pure Nothing
            let KoreParserOptions{willPrintDefinition} = koreParserOptions
            let KoreParserOptions{appKore} = koreParserOptions
            when (willPrintDefinition && not appKore) $
                putDebug parsedDefinition
            when appKore $ for_ indexedModules printAppKore
            pure indexedModules

        let KoreParserOptions{patternOpt} = koreParserOptions
        for_ patternOpt $ \patternOptions -> do
            let PatternOptions{mainModuleName} = patternOptions
                moduleName = ModuleName mainModuleName
            indexedModule <-
                traverse (lookupMainModule moduleName) indexedModules
            let PatternOptions{patternFileNames} = patternOptions
            for_ patternFileNames $ \patternFileName -> do
                parsedPattern <- mainPatternParse patternFileName
                verifyPattern indexedModule parsedPattern
                let KoreParserOptions{willPrintPattern} = koreParserOptions
                when willPrintPattern $ putDebug parsedPattern

{- | IO action that parses a kore definition from a filename and prints timing
 information.
-}
mainDefinitionParse :: FilePath -> Main ParsedDefinition
mainDefinitionParse = mainParse parseKoreDefinition

{- | IO action that parses a kore pattern from a filename and prints timing
 information.
-}
mainPatternParse :: FilePath -> Main ParsedPattern
mainPatternParse = mainParse parseKorePattern

{- | IO action verifies well-formedness of Kore definition and prints
 timing information.
-}
mainVerify ::
    -- | Parsed definition to check well-formedness
    ParsedDefinition ->
    IO (Map.Map ModuleName (VerifiedModule Attribute.Symbol))
mainVerify definition = flip runLoggerT Log.emptyLogger $ do
    verifyResult <-
        clockSomething
            "Verifying the definition"
            ( verifyAndIndexDefinition
                Builtin.koreVerifiers
                definition
            )
    either errorVerify return verifyResult

{- | Validate a pattern relative to the provided module.

If the module is not provided, no validation is performed.
-}
verifyPattern ::
    -- | Module containing definitions visible in the pattern.
    Maybe (VerifiedModule Attribute.Symbol) ->
    -- | Parsed pattern to check well-formedness
    ParsedPattern ->
    Main ()
verifyPattern Nothing _ = pure ()
verifyPattern (Just verifiedModule) patt = do
    verifyResult <-
        PatternVerifier.verifyStandalonePattern Nothing patt
            & PatternVerifier.runPatternVerifier context
            & clockSomething "Verifying the pattern"
    either errorVerify (\_ -> pure ()) verifyResult
  where
    context =
        PatternVerifier.verifiedModuleContext verifiedModule
            & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers

-- | Print the valid definition in Applicative Kore syntax.
printAppKore ::
    MonadIO io =>
    Map.Map ModuleName (VerifiedModule Attribute.Symbol) ->
    io ()
printAppKore =
    liftIO
        . putStrLn
        . unparseToString2
        . completeDefinition
        . toVerifiedDefinition

-- | Print any 'Debug'-able type.
putDebug :: Debug a => MonadIO io => a -> io ()
putDebug = liftIO . putDoc . debug

runEmptyLogger :: Main a -> IO a
runEmptyLogger = flip runLoggerT Log.emptyLogger
