module Main (main) where

import Control.Applicative
    ( Alternative (..)
    , optional
    )
import Control.Monad.Catch
    ( MonadCatch
    )
import Control.Monad.IO.Class
    ( MonadIO
    )
import Control.Monad.IO.Unlift
    ( MonadUnliftIO
    )
import qualified Control.Monad.Reader.Class as Reader
import Control.Monad.Trans
    ( lift
    )
import qualified Data.Char as Char
import qualified Data.Foldable as Foldable
import Data.List
    ( intercalate
    )
import Data.Reflection
import Data.Semigroup
    ( (<>)
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
    ( null
    , split
    )
import qualified Data.Text.IO as Text
    ( putStrLn
    , readFile
    )
import Data.Text.Prettyprint.Doc
    ( Doc
    , vsep
    )
import Data.Text.Prettyprint.Doc.Render.Text
    ( hPutDoc
    , putDoc
    )
import Options.Applicative
    ( InfoMod
    , Parser
    , argument
    , auto
    , fullDesc
    , header
    , help
    , long
    , metavar
    , option
    , progDesc
    , readerError
    , str
    , strOption
    , value
    )
import qualified Options.Applicative as Options
import System.Exit
    ( ExitCode (..)
    , exitWith
    )
import System.IO
    ( IOMode (WriteMode)
    , withFile
    )

import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Symbol as Attribute
import Kore.Error
    ( printError
    )
import Kore.Exec
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
    ( build
    )
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import Kore.Internal.TermLike
import Kore.Logger.Output
    ( KoreLogOptions (..)
    , LogMessage
    , LoggerT (..)
    , WithLog
    , parseKoreLogOptions
    , runLoggerT
    )
import qualified Kore.ModelChecker.Bounded as Bounded
    ( CheckResult (..)
    )
import Kore.Parser
    ( ParsedPattern
    , parseKorePattern
    )
import Kore.Predicate.Predicate
    ( makePredicate
    )
import Kore.Profiler.Data
    ( MonadProfiler
    )
import Kore.Step
import Kore.Step.Search
    ( SearchType (..)
    )
import qualified Kore.Step.Search as Search
import Kore.Step.SMT.Lemma
import Kore.Syntax.Definition
    ( ModuleName (..)
    )
import Kore.Unparser
    ( unparse
    )
import SMT
    ( MonadSMT
    )
import qualified SMT

import GlobalMain

{-
Main module to run kore-exec
TODO: add command line argument tab-completion
-}

data KoreSearchOptions =
    KoreSearchOptions
        { searchFileName :: !FilePath
        -- ^ Name of file containing a pattern to match during execution
        , bound :: !(Limit Natural)
        -- ^ The maximum bound on the number of search matches
        , searchType :: !SearchType
        -- ^ The type of search to perform
        }

parseKoreSearchOptions :: Parser KoreSearchOptions
parseKoreSearchOptions =
    KoreSearchOptions
    <$> strOption
        (  metavar "SEARCH_FILE"
        <> long "search"
        <> help "Kore source file representing pattern to search for. \
                \Needs --module."
        )
    <*> parseBound
    <*> parseSearchType
  where
    parseBound = Limit <$> bound <|> pure Unlimited
    bound =
        option auto
            (  metavar "BOUND"
            <> long "bound"
            <> help "Maximum number of solutions."
            )
    parseSearchType =
        parseSum
            "SEARCH_TYPE"
            "searchType"
            "Search type (selects potential solutions)"
            (map (\s -> (show s, s)) [ ONE, FINAL, STAR, PLUS ])

parseSum
    :: Eq value
    => String -> String -> String -> [(String, value)] -> Parser value
parseSum metaName longName helpMsg options =
    option (readSum longName options)
        (  metavar metaName
        <> long longName
        <> help (helpMsg <> ": " <> knownOptions)
        )
  where
    knownOptions = intercalate ", " (map fst options)

readSum :: String -> [(String, value)] -> Options.ReadM value
readSum longName options = do
    opt <- str
    case lookup opt options of
        Just val -> pure val
        _ -> readerError (unknown opt ++ known)
  where
    knownOptions = intercalate ", " (map fst options)
    unknown opt = "Unknown " ++ longName ++ " '" ++ opt ++ "'. "
    known = "Known " ++ longName ++ "s are: " ++ knownOptions ++ "."

applyKoreSearchOptions
    :: Maybe KoreSearchOptions
    -> KoreExecOptions
    -> KoreExecOptions
applyKoreSearchOptions Nothing koreExecOpts = koreExecOpts
applyKoreSearchOptions koreSearchOptions@(Just koreSearchOpts) koreExecOpts =
    koreExecOpts
        { koreSearchOptions
        , strategy =
            -- Search relies on exploring the entire space of states.
            allRewrites
        , stepLimit = min stepLimit searchTypeStepLimit
        }
  where
    KoreSearchOptions { searchType } = koreSearchOpts
    KoreExecOptions { stepLimit } = koreExecOpts
    searchTypeStepLimit =
        case searchType of
            ONE -> Limit 1
            _ -> Unlimited

-- | Available SMT solvers
data Solver = Z3 | None
    deriving (Eq, Ord, Show)
    deriving (Enum, Bounded)

parseSolver :: Parser Solver
parseSolver =
    option (readSum longName options)
    $  metavar "SOLVER"
    <> long longName
    <> help ("SMT solver for checking constraints: " <> knownOptions)
    <> value Z3
  where
    longName = "smt"
    knownOptions = intercalate ", " (map fst options)
    options = [ (map Char.toLower $ show s, s) | s <- [minBound .. maxBound] ]

-- | Main options record
data KoreExecOptions = KoreExecOptions
    { definitionFileName  :: !FilePath
    -- ^ Name for a file containing a definition to verify and use for execution
    , patternFileName     :: !(Maybe FilePath)
    -- ^ Name for file containing a pattern to verify and use for execution
    , outputFileName      :: !(Maybe FilePath)
    -- ^ Name for file to contain the output pattern
    , mainModuleName      :: !ModuleName
    -- ^ The name of the main module in the definition
    , smtTimeOut          :: !SMT.TimeOut
    , smtPrelude          :: !(Maybe FilePath)
    , smtSolver           :: !Solver
    , stepLimit           :: !(Limit Natural)
    , strategy            :: !([Rewrite] -> Strategy (Prim Rewrite))
    , koreLogOptions      :: !KoreLogOptions
    , koreSearchOptions   :: !(Maybe KoreSearchOptions)
    , koreProveOptions    :: !(Maybe KoreProveOptions)
    , koreMergeOptions    :: !(Maybe KoreMergeOptions)
    }

-- | Command Line Argument Parser
parseKoreExecOptions :: Parser KoreExecOptions
parseKoreExecOptions =
    applyKoreSearchOptions
        <$> optional parseKoreSearchOptions
        <*> parseKoreExecOptions0
  where
    parseKoreExecOptions0 :: Parser KoreExecOptions
    parseKoreExecOptions0 =
        KoreExecOptions
        <$> argument str
            (  metavar "DEFINITION_FILE"
            <> help "Kore definition file to verify and use for execution" )
        <*> optional
            (strOption
                (  metavar "PATTERN_FILE"
                <> long "pattern"
                <> help
                    "Verify and execute the Kore pattern found in PATTERN_FILE."
                )
            )
        <*> optional
            (strOption
                (  metavar "PATTERN_OUTPUT_FILE"
                <> long "output"
                <> help "Output file to contain final Kore pattern."
                )
            )
        <*> parseMainModuleName
        <*> option readSMTTimeOut
            ( metavar "SMT_TIMEOUT"
            <> long "smt-timeout"
            <> help "Timeout for calls to the SMT solver, in milliseconds"
            <> value defaultTimeOut
            )
        <*> optional
            ( strOption
                ( metavar "SMT_PRELUDE"
                <> long "smt-prelude"
                <> help "Path to the SMT prelude file"
                )
            )
        <*> parseSolver
        <*> parseStepLimit
        <*> parseStrategy
        <*> parseKoreLogOptions
        <*> pure Nothing
        <*> optional parseKoreProveOptions
        <*> optional parseKoreMergeOptions
    SMT.Config { timeOut = defaultTimeOut } = SMT.defaultConfig
    readSMTTimeOut = do
        i <- auto
        if i <= 0
            then readerError "smt-timeout must be a positive integer."
            else return $ SMT.TimeOut $ Limit i
    parseStepLimit = Limit <$> depth <|> pure Unlimited
    parseStrategy =
        option (readSum "strategy" strategies)
            (  metavar "STRATEGY"
            <> long "strategy"
            -- TODO (thomas.tuegel): Make defaultStrategy the default when it
            -- works correctly.
            <> value anyRewrite
            <> help "Select rewrites using STRATEGY."
            )
      where
        strategies =
            [ ("any", anyRewrite)
            , ("all", allRewrites)
            , ("any-heating-cooling", heatingCooling anyRewrite)
            , ("all-heating-cooling", heatingCooling allRewrites)
            ]
    depth =
        option auto
            (  metavar "DEPTH"
            <> long "depth"
            <> help "Execute up to DEPTH steps."
            )
    parseMainModuleName =
        ModuleName <$> strOption info
      where
        info =
            mconcat
                [ metavar "MODULE"
                , long "module"
                , help "The name of the main module in the Kore definition."
                ]

-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
    <> progDesc "Uses Kore definition in DEFINITION_FILE to execute pattern \
                \in PATTERN_FILE."
    <> header "kore-exec - an interpreter for Kore definitions"

-- TODO(virgil): Maybe add a regression test for main.
-- | Loads a kore definition file and uses it to execute kore programs
main :: IO ()
main = do
    options <- mainGlobal parseKoreExecOptions parserInfoModifiers
    Foldable.forM_ (localOptions options) mainWithOptions

mainWithOptions :: KoreExecOptions -> IO ()
mainWithOptions execOptions@KoreExecOptions { koreLogOptions } =
    (=<<) exitWith $ runLoggerT koreLogOptions $ case () of
    ()
      | Just proveOptions <- koreProveOptions execOptions ->
        koreProve execOptions proveOptions

      | Just searchOptions <- koreSearchOptions execOptions ->
        koreSearch execOptions searchOptions

      | Just mergeOptions <- koreMergeOptions execOptions ->
        koreMerge execOptions mergeOptions

      | otherwise ->
        koreRun execOptions

koreSearch :: KoreExecOptions -> KoreSearchOptions -> Main ExitCode
koreSearch execOptions searchOptions = do
    let KoreExecOptions { definitionFileName } = execOptions
    definition <- loadDefinitions [definitionFileName]
    let KoreExecOptions { mainModuleName } = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreSearchOptions { searchFileName } = searchOptions
    target <- mainParseSearchPattern mainModule searchFileName
    let KoreExecOptions { patternFileName } = execOptions
    initial <- loadPattern mainModule patternFileName
    final <- execute execOptions mainModule $ do
        search mainModule strategy' initial target config
    lift $ renderResult execOptions (unparse final)
    return ExitSuccess
  where
    KoreSearchOptions { bound, searchType } = searchOptions
    config = Search.Config { bound, searchType }
    KoreExecOptions { stepLimit, strategy } = execOptions
    strategy' = Limit.replicate stepLimit . strategy

koreRun :: KoreExecOptions -> Main ExitCode
koreRun execOptions = do
    let KoreExecOptions { definitionFileName } = execOptions
    definition <- loadDefinitions [definitionFileName]
    let KoreExecOptions { mainModuleName } = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreExecOptions { patternFileName } = execOptions
    initial <- loadPattern mainModule patternFileName
    (exitCode, final) <- execute execOptions mainModule $ do
        final <- exec mainModule strategy' initial
        exitCode <- execGetExitCode mainModule strategy' final
        return (exitCode, final)
    lift $ renderResult execOptions (unparse final)
    return exitCode
  where
    KoreExecOptions { stepLimit, strategy } = execOptions
    strategy' = Limit.replicate stepLimit . strategy

koreProve :: KoreExecOptions -> KoreProveOptions -> Main ExitCode
koreProve execOptions proveOptions = do
    let KoreExecOptions { definitionFileName } = execOptions
        KoreProveOptions { specFileName } = proveOptions
    definition <- loadDefinitions [definitionFileName, specFileName]
    let KoreExecOptions { mainModuleName } = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreProveOptions { specMainModule } = proveOptions
    specModule <- loadModule specMainModule definition
    (exitCode, final) <- execute execOptions mainModule $ do
        let KoreExecOptions { stepLimit } = execOptions
            KoreProveOptions { graphSearch, bmc } = proveOptions
        if bmc
            then do
                checkResult <-
                    boundedModelCheck
                        stepLimit
                        mainModule
                        specModule
                        graphSearch
                case checkResult of
                    Bounded.Proved -> return success
                    Bounded.Unknown -> return unknown
                    Bounded.Failed final -> return (failure final)
            else
                either failure (const success)
                <$> prove stepLimit mainModule specModule
    lift $ renderResult execOptions (unparse final)
    return exitCode
  where
    failure pat = (ExitFailure 1, pat)
    success = (ExitSuccess, mkTop $ mkSortVariable "R")
    unknown =
        ( ExitSuccess
        , mkElemVar $ elemVarS "Unknown" (mkSort $ noLocationId "SortUnknown")
        )

koreMerge :: KoreExecOptions -> KoreMergeOptions -> Main ExitCode
koreMerge execOptions mergeOptions = do
    let KoreExecOptions {definitionFileName} = execOptions
    definition <- loadDefinitions [definitionFileName]
    let KoreExecOptions {mainModuleName} = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreMergeOptions {rulesFileName} = mergeOptions
    ruleIds <- lift $ loadRuleIds rulesFileName
    eitherMergedRule <- execute execOptions mainModule $
        mergeRules mainModule ruleIds
    case eitherMergedRule of
        (Left err) -> do
            lift $ Text.putStrLn err
            return (ExitFailure 1)
        (Right mergedRule) -> do
            lift $ renderResult execOptions (vsep (map unparse mergedRule))
            return ExitSuccess

loadRuleIds :: FilePath -> IO [Text]
loadRuleIds fileName = do
    fileContents <- Text.readFile fileName
    return
        (filter
            (not . Text.null)
            (Text.split (`elem` (" \t\n\r" :: String)) fileContents)
        )

type MonadExecute exe =
    ( MonadCatch exe
    , MonadIO exe
    , MonadProfiler exe
    , MonadSMT exe
    , MonadUnliftIO exe
    , WithLog LogMessage exe
    )

-- | Run the worker in the context of the main module.
execute
    :: forall r
    .  KoreExecOptions
    -> LoadedModule  -- ^ Main module
    -> (forall exe. MonadExecute exe => exe r)  -- ^ Worker
    -> Main r
execute options mainModule worker = do
    logger <- LoggerT Reader.ask
    clockSomethingIO "Executing"
        $ case smtSolver of
            Z3   -> withZ3 logger
            None -> withoutSMT logger
  where
    withZ3 logger =
        SMT.runSMT config logger $ do
            give (MetadataTools.build mainModule) (declareSMTLemmas mainModule)
            worker
    withoutSMT logger = SMT.runNoSMT logger worker
    KoreExecOptions { smtTimeOut, smtPrelude, smtSolver } = options
    config =
        SMT.defaultConfig
            { SMT.timeOut = smtTimeOut
            , SMT.preludeFile = smtPrelude
            }

loadPattern :: LoadedModule -> Maybe FilePath -> Main (TermLike Variable)
loadPattern mainModule (Just fileName) =
    mainPatternParseAndVerify mainModule fileName
loadPattern _ Nothing = error "Missing: --pattern PATTERN_FILE"

-- | IO action that parses a kore pattern from a filename and prints timing
-- information.
mainPatternParse :: String -> Main ParsedPattern
mainPatternParse = mainParse parseKorePattern

renderResult :: KoreExecOptions -> Doc ann -> IO ()
renderResult KoreExecOptions { outputFileName } doc =
    case outputFileName of
        Nothing -> putDoc doc
        Just outputFile -> withFile outputFile WriteMode (`hPutDoc` doc)

-- | IO action that parses a kore pattern from a filename, verifies it,
-- converts it to a pure patterm, and prints timing information.
mainPatternParseAndVerify
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> String
    -> Main (TermLike Variable)
mainPatternParseAndVerify indexedModule patternFileName =
    mainPatternParse patternFileName >>= mainPatternVerify indexedModule

mainParseSearchPattern
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> String
    -> Main (Pattern Variable)
mainParseSearchPattern indexedModule patternFileName = do
    purePattern <- mainPatternParseAndVerify indexedModule patternFileName
    case purePattern of
        And_ _ term predicateTerm -> return
            Conditional
                { term
                , predicate =
                    either (error . printError) id
                        (makePredicate predicateTerm)
                , substitution = mempty
                }
        _ -> error "Unexpected non-conjunctive pattern"
