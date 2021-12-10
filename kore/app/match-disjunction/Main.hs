module Main (main) where

import GlobalMain
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import Kore.BugReport
import Kore.Exec (matchDisjunction)
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Internal.Pattern (Pattern)
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike (
    pattern Or_,
 )
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
exeName = ExeName "kore-match-disjunction"

envName :: String
envName = "KORE_MATCH_DISJUNCTION_OPTS"

data KoreMatchDisjunctionOptions = KoreMatchDisjunctionOptions
    { definitionFileName :: !FilePath
    -- ^ Name of file containing a definition to verify and use for execution
    , disjunctionFileName :: !FilePath
    -- ^ Name of file containing a disjunction to verify and use for matching
    , matchFileName :: !FilePath
    -- ^ Name of file used to match with disjunction
    , outputFileName :: !(Maybe FilePath)
    -- ^ Name for file to contain the output pattern
    , mainModuleName :: !ModuleName
    -- ^ The name of the main module in the definition
    , bugReportOption :: !BugReportOption
    , koreLogOptions :: !KoreLogOptions
    }

parseKoreMatchDisjunctionOptions :: TimeSpec -> Parser KoreMatchDisjunctionOptions
parseKoreMatchDisjunctionOptions startTime =
    KoreMatchDisjunctionOptions
        <$> argument
            str
            ( metavar "DEFINITION_FILE"
                <> help "Kore definition file to verify and use for execution."
            )
        <*> strOption
            ( metavar "DISJUNCTION_FILE"
                <> long "disjunction"
                <> help "File containing a disjunction of concrete terms."
            )
        <*> strOption
            ( metavar "MATCH_FILE"
                <> long "match"
                <> help "Kore source file representing pattern to search for."
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
        <> progDesc "Matches Kore pattern in MATCH_FILE with Kore pattern in DISJUNCTION_FILE"
        <> header "kore-match-disjunction - a tool for applying search patterns to disjunctions of configurations"

main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <-
        mainGlobal
            exeName
            (Just envName)
            (parseKoreMatchDisjunctionOptions startTime)
            parserInfoModifiers
    for_ (localOptions options) mainWithOptions

mainWithOptions :: KoreMatchDisjunctionOptions -> IO ()
mainWithOptions options = do
    exitCode <-
        withBugReport exeName bugReportOption $ \tmpDir ->
            koreMatchDisjunction options
                & runKoreLog tmpDir koreLogOptions
    exitWith exitCode
  where
    KoreMatchDisjunctionOptions{bugReportOption} = options
    KoreMatchDisjunctionOptions{koreLogOptions} = options

koreMatchDisjunction :: KoreMatchDisjunctionOptions -> Main ExitCode
koreMatchDisjunction options = do
    definition <- loadDefinitions [definitionFileName]
    mainModule <- loadModule mainModuleName definition
    matchPattern <- mainParseMatchPattern mainModule matchFileName
    disjunctionPattern <-
        mainParseDisjunctionPattern mainModule disjunctionFileName
    final <-
        clockSomethingIO "Executing" $
            matchDisjunction mainModule matchPattern disjunctionPattern
    lift $
        renderResult
            options
            (unparse final)
    return ExitSuccess
  where
    mainParseMatchPattern mainModule fileName =
        mainParseSearchPattern mainModule fileName
            <&> mkRewritingPattern
    KoreMatchDisjunctionOptions
        { definitionFileName
        , disjunctionFileName
        , matchFileName
        , mainModuleName
        } = options

mainParseDisjunctionPattern ::
    VerifiedModule StepperAttributes ->
    String ->
    Main [Pattern RewritingVariableName]
mainParseDisjunctionPattern indexedModule patternFileName = do
    purePattern <- mainPatternParseAndVerify indexedModule patternFileName
    return $ parseDisjunction purePattern
  where
    parseDisjunction (Or_ _ term1 term2) =
        parseDisjunction term1 <> parseDisjunction term2
    parseDisjunction term =
        let patt =
                mkRewritingPattern
                    . Pattern.fromTermLike
                    $ term
         in [patt]

renderResult :: KoreMatchDisjunctionOptions -> Doc ann -> IO ()
renderResult KoreMatchDisjunctionOptions{outputFileName} doc =
    case outputFileName of
        Nothing -> putDoc doc
        Just outputFile ->
            withFile outputFile WriteMode (`hPutDoc` doc)
