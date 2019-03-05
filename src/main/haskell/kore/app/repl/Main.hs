module Main (main) where

import           Control.Applicative
                 ( optional )
import qualified Control.Lens as Lens
import           Data.Function
                 ( (&) )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Semigroup
                 ( (<>) )
import           Data.Text
                 ( Text )
import           Options.Applicative
                 ( InfoMod, Parser, argument, auto, fullDesc, header, help,
                 long, metavar, option, progDesc, readerError, str, strOption,
                 value )

import           Data.Limit
                 ( Limit (..) )
import           Kore.AST.Pure
                 ( AstLocation, getId )
import           Kore.AST.Sentence
                 ( KoreDefinition, ModuleName (..), getModuleNameForError )
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (DoNotVerifyAttributes),
                 defaultAttributesVerification,
                 verifyAndIndexDefinitionWithBase )
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( printError )
import           Kore.Exec
                 ( proveWithRepl )
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), VerifiedModule )
import           Kore.Logger.Output
                 ( emptyLogger )
import           Kore.Parser.Parser
                 ( parseKoreDefinition, parseKorePattern )
import           Kore.Step.AxiomPatterns
                 ( AxiomPatternAttributes )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.StepperAttributes
import qualified SMT

import GlobalMain

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
    }

parseKoreReplOptions :: Parser KoreReplOptions
parseKoreReplOptions =
    KoreReplOptions
    <$> parseModule
        "main"
        "Kore definition file to verify and use for execution"
    <*> parseModule
        "claim"
        "Kore source file representing spec to be proven"
    <*> parseSmtOptions

  where

    parseModule :: String -> String -> Parser KoreModule
    parseModule name helpMessage =
        KoreModule
        <$> argument str
            (  metavar (name <> "_DEFINITION_FILE")
            <> help helpMessage
            )
        <*> parseModuleName name helpMessage

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

    parseModuleName :: String -> String -> Parser ModuleName
    parseModuleName name helpMessage =
        ModuleName
        <$> argument str
            (  metavar (name <> "_MODULE")
            <> help helpMessage
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



constructorFunctions
    :: VerifiedModule StepperAttributes AxiomPatternAttributes
    -> VerifiedModule StepperAttributes AxiomPatternAttributes
constructorFunctions ixm =
    ixm
        { indexedModuleObjectSymbolSentences =
            Map.mapWithKey
                constructorFunctions1
                (indexedModuleObjectSymbolSentences ixm)
        , indexedModuleObjectAliasSentences =
            Map.mapWithKey
                constructorFunctions1
                (indexedModuleObjectAliasSentences ixm)
        , indexedModuleImports = recurseIntoImports <$> indexedModuleImports ixm
        }
  where
    constructorFunctions1 ident (atts, defn) =
        ( atts
            & lensConstructor Lens.<>~ Constructor isCons
            & lensFunctional Lens.<>~ Functional (isCons || isInj)
            & lensInjective Lens.<>~ Injective (isCons || isInj)
            & lensSortInjection Lens.<>~ SortInjection isInj
        , defn
        )
      where
        isInj = getId ident == "inj"
        isCons = elem (getId ident) ["kseq", "dotk"]

    recurseIntoImports (attrs, attributes, importedModule) =
        (attrs, attributes, constructorFunctions importedModule)

mainModule
    :: ModuleName
    -> Map.Map
        ModuleName
        (VerifiedModule StepperAttributes AxiomPatternAttributes)
    -> IO (VerifiedModule StepperAttributes AxiomPatternAttributes)
mainModule name modules =
    case Map.lookup name modules of
        Nothing ->
            error
                (  "The main module, '"
                ++ getModuleNameForError name
                ++ "', was not found. Check the --module flag."
                )
        Just m -> return m

verifyDefinitionWithBase
    :: Maybe
        ( Map.Map
            ModuleName
            (VerifiedModule StepperAttributes AxiomPatternAttributes)
        , Map.Map Text AstLocation
        )
    -- ^ base definition to use for verification
    -> Bool -- ^ whether to check (True) or ignore attributes during verification
    -> KoreDefinition -- ^ Parsed definition to check well-formedness
    -> IO
        ( Map.Map
            ModuleName
            (VerifiedModule StepperAttributes AxiomPatternAttributes)
        , Map.Map Text AstLocation
        )
verifyDefinitionWithBase maybeBaseModule willChkAttr definition =
    let attributesVerification =
            if willChkAttr
            then defaultAttributesVerification Proxy Proxy
            else DoNotVerifyAttributes
    in do
      verifyResult <-
        clockSomething "Verifying the definition"
            (verifyAndIndexDefinitionWithBase
                maybeBaseModule
                attributesVerification
                Builtin.koreVerifiers
                definition
            )
      case verifyResult of
        Left err1               -> error (printError err1)
        Right indexedDefinition -> return indexedDefinition

parseDefinition :: FilePath -> IO KoreDefinition
parseDefinition = mainParse parseKoreDefinition

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
