module Main (main) where

import GlobalMain
import qualified GlobalMain
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import Kore.BugReport
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.TermLike (VariableName, pattern Or_)
import Kore.Log (KoreLogOptions, parseKoreLogOptions, runKoreLog)
import Kore.Syntax.Module (ModuleName (..))
import Options.Applicative (InfoMod, Parser, argument, fullDesc, header, help, long, metavar, progDesc, str, strOption)
import Prelude.Kore
import System.Clock (Clock (..), TimeSpec, getTime)
import System.Exit (ExitCode, exitWith)

exeName :: ExeName
exeName = ExeName "kore-match-disjunction"

envName :: String
envName = "KORE_MATCH_DISJUNCTION_OPTS"

data KoreMatchDisjunctionOptions = KoreMatchDisjunctionOptions
    { -- | Name of file containing a definition to verify and use for execution
      definitionFileName :: !FilePath
    , -- | Name of file containing a disjunction to verify and use for matching
      disjunctionFileName :: !FilePath
    , -- | Name of file used to match with disjunction
      matchFileName :: !FilePath
    , -- | Name for file to contain the output pattern
      outputFileName :: !(Maybe FilePath)
    , -- | The name of the main module in the definition
      mainModuleName :: !ModuleName
    , bugReportOption :: !BugReportOption
    , koreLogOptions :: !KoreLogOptions
    }

parseKoreMatchDisjunctionOptions :: TimeSpec -> Parser KoreMatchDisjunctionOptions
parseKoreMatchDisjunctionOptions startTime =
    KoreMatchDisjunctionOptions
        <$> argument
            str
            ( metavar "DEFINITION_FILE"
                <> help "Kore definition file to verify and use for execution"
            )
        <*> strOption
            ( metavar "DISJUNCTION_FILE"
                <> long "disjunction"
                <> help "TODO"
            )
        <*> strOption
            ( metavar "MATCH_FILE"
                <> long "match"
                <> help "TODO"
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
    -- TODO: factor this out in GlobalMain?
    parseMainModuleName =
        GlobalMain.parseModuleName
            "MODULE"
            "module"
            "The name of the main module in the Kore definition."

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> progDesc "Matches Kore pattern in MATCH_FILE with Kore pattern in DISJUNCTION_FILE"
        <> header "kore-match-disjunction - TODO"

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
    -- TODO: do we wanna do some simplification of the disjunction
    -- pattern, since the simplifier will return a list of patterns,
    -- and then we can match on this?
    disjunctionPattern <-
        mainParseDisjunctionPattern mainModule disjunctionFileName
    undefined
  where
    mainParseMatchPattern = mainParseSearchPattern
    KoreMatchDisjunctionOptions
        { definitionFileName
        , disjunctionFileName
        , matchFileName
        , outputFileName
        , mainModuleName
        } = options

mainParseDisjunctionPattern ::
    VerifiedModule StepperAttributes ->
    String ->
    Main [Pattern VariableName]
mainParseDisjunctionPattern indexedModule patternFileName = do
    purePattern <- mainPatternParseAndVerify indexedModule patternFileName
    return $ parseDisjunction purePattern
  where
    parseDisjunction = undefined
