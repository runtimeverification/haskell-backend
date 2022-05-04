module Main (main) where

import GlobalMain
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import Kore.BugReport
import Kore.Exec (simplify)
import Kore.IndexedModule.IndexedModule (
    IndexedModule (..),
    VerifiedModule,
 )
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.Pattern qualified as Pattern
import Kore.Log (
    KoreLogOptions,
    parseKoreLogOptions,
    runKoreLog,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkRewritingPattern,
 )
import Kore.Syntax.Module (
    ModuleName (..),
 )
import Kore.Unparser (
    unparse,
 )
import Options.Applicative (
    InfoMod,
    Parser,
    argument,
    fullDesc,
    header,
    help,
    long,
    metavar,
    progDesc,
    str,
    strOption,
 )
import Prelude.Kore
import Pretty
import System.Clock (
    Clock (..),
    TimeSpec,
    getTime,
 )
import System.Exit (
    exitWith,
 )
import System.IO (
    IOMode (WriteMode),
    withFile,
 )

exeName :: ExeName
exeName = ExeName "kore-simplify"

envName :: String
envName = "KORE_SIMPLIFY_OPTS"

data KoreSimplifyOptions = KoreSimplifyOptions
    { -- | Name of file containing a definition to verify
      definitionFileName :: !FilePath
    , -- | Name of file containing a pattern to verify and simplify
      patternFileName :: !FilePath
    , -- | Name for file to contain the output pattern
      outputFileName :: !(Maybe FilePath)
    , -- | The name of the main module in the definition
      mainModuleName :: !ModuleName
    , bugReportOption :: !BugReportOption
    , koreLogOptions :: !KoreLogOptions
    }

parseKoreSimplifyOptions :: TimeSpec -> Parser KoreSimplifyOptions
parseKoreSimplifyOptions startTime =
    KoreSimplifyOptions
        <$> argument
            str
            ( metavar "DEFINITION_FILE"
                <> help "Kore definition file to verify and use for execution."
            )
        <*> strOption
            ( metavar "PATTERN_INPUT_FILE"
                <> long "pattern"
                <> help "File containing a pattern."
            )
        <*> optional
            ( strOption
                ( metavar "PATTERN_OUTPUT_FILE"
                    <> long "output"
                    <> help "Output file to contain final Kore pattern."
                )
            )
        <*> parseMainModuleName
        <*> parseBugReportOption
        <*> parseKoreLogOptions exeName startTime
  where
    parseMainModuleName =
        GlobalMain.parseModuleName
            "MODULE"
            "module"
            "The name of the main module in the Kore definition."

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> progDesc "Simplifies and validates the Kore pattern in PATTERN_INPUT_FILE"
        <> header "kore-simplify - a tool for simplifying patterns"

main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <-
        mainGlobal
            exeName
            (Just envName)
            (parseKoreSimplifyOptions startTime)
            parserInfoModifiers
    for_ (localOptions options) mainWithOptions

mainWithOptions :: LocalOptions KoreSimplifyOptions -> IO ()
mainWithOptions localOptions@LocalOptions{execOptions} = do
    exitCode <-
        withBugReport exeName bugReportOption $ \tmpDir ->
            koreSimplify localOptions
                & runKoreLog tmpDir koreLogOptions
    exitWith exitCode
  where
    KoreSimplifyOptions{bugReportOption, koreLogOptions} = execOptions

koreSimplify :: LocalOptions KoreSimplifyOptions -> Main ExitCode
koreSimplify LocalOptions{execOptions} = do
    definition <- loadDefinitions [definitionFileName]
    mainModule <- loadModule mainModuleName definition
    inputPattern <-
        mainParseInputPattern mainModule patternFileName
    final <- simplify inputPattern
    lift $
        renderResult
            execOptions
            (unparse final)
    return ExitSuccess
  where
    KoreSimplifyOptions
        { definitionFileName
        , patternFileName
        , mainModuleName
        } = execOptions

mainParseInputPattern ::
    VerifiedModule StepperAttributes ->
    String ->
    Main (Pattern RewritingVariableName)
mainParseInputPattern indexedModule patternFileName = do
    purePattern <- mainPatternParseAndVerify (indexedModuleSyntax indexedModule) patternFileName
    return $ parsePattern purePattern
  where
    parsePattern = mkRewritingPattern . Pattern.fromTermLike

renderResult :: KoreSimplifyOptions -> Doc ann -> IO ()
renderResult KoreSimplifyOptions{outputFileName} doc =
    case outputFileName of
        Nothing -> putDoc doc
        Just outputFile ->
            withFile outputFile WriteMode (`hPutDoc` doc)
