{-# OPTIONS_GHC -Wno-unused-top-binds    #-}
-- Added for outputFileName

module Main (main) where

import Control.Applicative
       ( optional )
import Data.Semigroup
       ( (<>) )
import Options.Applicative
       ( InfoMod, Parser, argument, auto, fullDesc, header, help, long,
       metavar, option, progDesc, readerError, str, strOption, value )

import Data.Limit
       ( Limit (..) )
import Kore.AST.Sentence
       ( ModuleName (..) )
import Kore.Exec
       ( proveWithRepl )
import Kore.Logger.Output
       ( emptyLogger )
import Kore.Step.Simplification.Data
       ( evalSimplifier )

import           GlobalMain
import qualified SMT as SMT

-- | Represents a file name along with its module name passed.
data KoreModule = KoreModule
    { fileName   :: !FilePath
    , moduleName :: !ModuleName
    }

-- | SMT Timeout and (optionally) a custom prelude path.
data SmtOptions = SmtOptions
    { timeOut :: !SMT.TimeOut
    , prelude :: !(Maybe FilePath)
    }

-- | Options for the kore repl.
data KoreReplOptions = KoreReplOptions
    { definitionModule :: !KoreModule
    , specModule       :: !KoreModule
    , smtOptions       :: !SmtOptions
    , outputFileName   :: !(Maybe FilePath)
    }

parseKoreReplOptions :: Parser KoreReplOptions
parseKoreReplOptions =
    KoreReplOptions
    <$> parseMainModule
    <*> parseSpecModule
    <*> parseSmtOptions
    <*> optional
            (strOption
                (  metavar "PATTERN_OUTPUT_FILE"
                <> long "output"
                <> help "Output file to contain final Kore pattern."
                )
            )
  where
    parseMainModule :: Parser KoreModule
    parseMainModule  =
        KoreModule
        <$> argument str
            (  metavar ("MAIN_DEFINITION_FILE")
            <> help "Kore definition file to verify and use for execution"
            )
        <*> parseModuleName "MAIN" "Kore main module name." "module"

    parseSpecModule :: Parser KoreModule
    parseSpecModule =
        KoreModule
        <$> strOption
            (  metavar ("SPEC_DEFINITION_FILE")
            <> long "prove"
            <> help "Spec definition file"
            )
        <*> parseModuleName "SPEC" "Spec module name" "spec-module"

    parseModuleName :: String -> String -> String -> Parser ModuleName
    parseModuleName name helpMessage longName =
        ModuleName
        <$> strOption
            (  metavar (name <> "_MODULE")
            <> long longName
            <> help helpMessage
            )

    parseSmtOptions :: Parser SmtOptions
    parseSmtOptions =
        SmtOptions
        <$> option readSMTTimeOut
            (  metavar "SMT_TIMEOUT"
            <> long "smt-timeout"
            <> help "Timeout for calls to the SMT solver, in miliseconds"
            <> value defaultTimeOut
            )
        <*> optional
            ( strOption
                (  metavar "SMT_PRELUDE"
                <> long "smt-prelude"
                <> help "Path to the SMT prelude file"
                )
            )

    SMT.Config { timeOut = defaultTimeOut } = SMT.defaultConfig

    readSMTTimeOut = do
        i <- auto
        if i <= 0
            then readerError "smt-timeout must be a positive integer."
            else return $ SMT.TimeOut $ Limit i

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
    <> progDesc "REPL debugger for proofs"
    <> header "kore-repl - a repl for Kore proofs"

main :: IO ()
main = do
    options <- mainGlobal parseKoreReplOptions parserInfoModifiers
    case localOptions options of
        Nothing -> pure ()
        Just koreReplOptions -> mainWithOptions koreReplOptions

mainWithOptions :: KoreReplOptions -> IO ()
mainWithOptions
    KoreReplOptions { definitionModule, specModule, smtOptions }
  = do
    parsedDefinition <- parseDefinition definitionFileName
    indexedDefinition@(indexedModules, _) <-
        verifyDefinitionWithBase
            Nothing
            True
            parsedDefinition
    indexedModule <-
        constructorFunctions <$> mainModule mainModuleName indexedModules

    specDef <- parseDefinition specFileName
    (specDefIndexedModules, _) <-
        verifyDefinitionWithBase
            (Just indexedDefinition)
            True
            specDef
    specDefIndexedModule <-
        mainModule specMainModule specDefIndexedModules

    let
        smtConfig =
            SMT.defaultConfig
                { SMT.timeOut = smtTimeOut
                , SMT.preludeFile = smtPrelude
                }
    SMT.runSMT smtConfig
        $ evalSimplifier emptyLogger
        $ proveWithRepl indexedModule specDefIndexedModule

  where
    mainModuleName :: ModuleName
    mainModuleName = moduleName definitionModule

    definitionFileName :: FilePath
    definitionFileName = fileName definitionModule

    specMainModule :: ModuleName
    specMainModule = moduleName specModule

    specFileName :: FilePath
    specFileName = fileName specModule

    smtTimeOut :: SMT.TimeOut
    smtTimeOut = timeOut smtOptions

    smtPrelude :: Maybe FilePath
    smtPrelude = prelude smtOptions
