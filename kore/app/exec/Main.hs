module Main (main) where

import Prelude.Kore

import Control.Monad.Catch
    ( MonadCatch
    , SomeException
    , displayException
    , handle
    , throwM
    )
import Control.Monad.Extra as Monad
import qualified Data.Char as Char
import Data.Default
    ( def
    )
import qualified Data.Foldable as Foldable
import Data.Limit
    ( Limit (..)
    , maybeLimit
    )
import Data.List
    ( intercalate
    )
import Data.Reflection
import Data.Semigroup
    ( (<>)
    )
import Data.Text
    ( Text
    , unpack
    )
import qualified Data.Text as Text
    ( null
    , split
    )
import qualified Data.Text.IO as Text
    ( putStrLn
    , readFile
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
import System.Directory
    ( copyFile
    , doesFileExist
    , emptyPermissions
    , setOwnerExecutable
    , setOwnerReadable
    , setOwnerSearchable
    , setOwnerWritable
    , setPermissions
    )
import System.Exit
    ( ExitCode (..)
    , exitWith
    )
import System.FilePath
    ( (</>)
    )
import System.IO
    ( IOMode (WriteMode)
    , withFile
    )

import qualified Data.Limit as Limit
import Kore.Attribute.Symbol as Attribute
import Kore.BugReport
import Kore.Exec
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    , indexedModuleRawSentences
    )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
    ( build
    )
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makePredicate
    )
import Kore.Internal.TermLike
    ( pattern And_
    , TermLike
    , VariableName
    , mkElemVar
    , mkElementVariable
    , mkSort
    , mkSortVariable
    , mkTop
    , noLocationId
    )
import Kore.Log
    ( ExeName (..)
    , KoreLogOptions (..)
    , LogMessage
    , SomeEntry (..)
    , WithLog
    , logEntry
    , parseKoreLogOptions
    , runKoreLog
    , unparseKoreLogOptions
    )
import Kore.Log.ErrorException
    ( errorException
    )
import qualified Kore.ModelChecker.Bounded as Bounded
    ( CheckResult (..)
    )
import Kore.Parser
    ( ParsedPattern
    , parseKorePattern
    )
import Kore.Profiler.Data
    ( MonadProfiler
    )
import Kore.Step
import Kore.Step.RulePattern
    ( ReachabilityRule
    )
import qualified Kore.Step.RulePattern as Rule
    ( toSentence
    )
import Kore.Step.Search
    ( SearchType (..)
    )
import qualified Kore.Step.Search as Search
import Kore.Step.SMT.Lemma
import Kore.Step.Strategy
    ( GraphSearchOrder (..)
    )
import qualified Kore.Strategies.Goal as Goal
import Kore.Strategies.Verification
    ( Stuck (..)
    )
import Kore.Syntax.Definition
    ( Definition (Definition)
    , Module (Module)
    , ModuleName (..)
    , Sentence (..)
    )
import qualified Kore.Syntax.Definition as Definition.DoNotUse
import Kore.Unparser
    ( unparse
    )
import Pretty
    ( Doc
    , Pretty (..)
    , hPutDoc
    , putDoc
    , vsep
    )
import SMT
    ( MonadSMT
    , TimeOut (..)
    )
import qualified SMT
import Stats

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

parseSum :: String -> String -> String -> [(String, value)] -> Parser value
parseSum metaName longName helpMsg options =
    option (snd <$> readSum longName options)
        (  metavar metaName
        <> long longName
        <> help (helpMsg <> ": " <> knownOptions)
        )
  where
    knownOptions = intercalate ", " (map fst options)

readSum :: String -> [(String, value)] -> Options.ReadM (String, value)
readSum longName options = do
    opt <- str
    case lookup opt options of
        Just val -> pure (opt, val)
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
            ("all", priorityAllStrategy)
        , depthLimit = min depthLimit searchTypeDepthLimit
        }
  where
    KoreSearchOptions { searchType } = koreSearchOpts
    KoreExecOptions { depthLimit } = koreExecOpts
    searchTypeDepthLimit =
        case searchType of
            ONE -> Limit 1
            _ -> Unlimited

-- | Available SMT solvers
data Solver = Z3 | None
    deriving (Eq, Ord, Show)
    deriving (Enum, Bounded)

parseSolver :: Parser Solver
parseSolver =
    option (snd <$> readSum longName options)
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
    , breadthLimit        :: !(Limit Natural)
    , depthLimit          :: !(Limit Natural)
    , strategy            :: !(String, [Rewrite] -> Strategy (Prim Rewrite))
    , koreLogOptions      :: !KoreLogOptions
    , koreSearchOptions   :: !(Maybe KoreSearchOptions)
    , koreProveOptions    :: !(Maybe KoreProveOptions)
    , koreMergeOptions    :: !(Maybe KoreMergeOptions)
    , rtsStatistics       :: !(Maybe FilePath)
    , bugReport           :: !BugReport
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
        <*> parseBreadthLimit
        <*> parseDepthLimit
        <*> parseStrategy
        <*> parseKoreLogOptions (ExeName "kore-exec")
        <*> pure Nothing
        <*> optional parseKoreProveOptions
        <*> optional parseKoreMergeOptions
        <*> optional parseRtsStatistics
        <*> parseBugReport
    SMT.Config { timeOut = defaultTimeOut } = SMT.defaultConfig
    readSMTTimeOut = do
        i <- auto
        if i <= 0
            then readerError "smt-timeout must be a positive integer."
            else return $ SMT.TimeOut $ Limit i
    parseBreadthLimit = Limit <$> breadth <|> pure Unlimited
    parseDepthLimit = Limit <$> depth <|> pure Unlimited
    parseStrategy =
        option (readSum "strategy" strategies)
            (  metavar "STRATEGY"
            <> long "strategy"
            -- TODO (thomas.tuegel): Make defaultStrategy the default when it
            -- works correctly.
            <> value ("any", priorityAnyStrategy)
            <> help "Select rewrites using STRATEGY."
            )
      where
        strategies =
            [ ("any", priorityAnyStrategy)
            , ("all", priorityAllStrategy)
            , ("any-heating-cooling", heatingCooling priorityAnyStrategy)
            , ("all-heating-cooling", heatingCooling priorityAllStrategy)
            ]
    breadth =
        option auto
            (  metavar "BREADTH"
            <> long "breadth"
            <> help "Allow up to BREADTH parallel execution branches."
            )
    depth =
        option auto
            (  metavar "DEPTH"
            <> long "depth"
            <> help "Execute up to DEPTH steps."
            )
    parseMainModuleName =
        GlobalMain.parseModuleName
            "MODULE"
            "module"
            "The name of the main module in the Kore definition."
    parseRtsStatistics =
        strOption (mconcat infos)
      where
        infos =
            [ metavar "FILENAME"
            , long "rts-statistics"
            , help "Write runtime statistics to FILENAME in JSON format."
            ]

-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
    <> progDesc "Uses Kore definition in DEFINITION_FILE to execute pattern \
                \in PATTERN_FILE."
    <> header "kore-exec - an interpreter for Kore definitions"

unparseKoreSearchOptions :: KoreSearchOptions -> [String]
unparseKoreSearchOptions (KoreSearchOptions _ bound searchType) =
    [ "--search searchFile.kore"
    , maybeLimit "" (\limit -> "--bound " <> show limit) bound
    , "--searchType " <> show searchType
    ]

unparseKoreMergeOptions :: KoreMergeOptions -> [String]
unparseKoreMergeOptions (KoreMergeOptions _ maybeBatchSize) =
    [ "--merge-rules mergeRules.kore"]
    <> maybe mempty ((:[]) . ("--merge-batch-size " <>) . show) maybeBatchSize

unparseKoreProveOptions :: KoreProveOptions -> [String]
unparseKoreProveOptions
    ( KoreProveOptions
        _
        (ModuleName moduleName)
        graphSearch
        bmc
        saveProofs
    )
  =
    [ "--prove spec.kore"
    , "--spec-module " <> unpack moduleName
    , "--graph-search "
        <> if graphSearch == DepthFirst then "depth-first" else "breadth-first"
    , if bmc then "--bmc" else ""
    , maybe "" ("--save-proofs " <>) saveProofs
    ]

koreExecSh :: KoreExecOptions -> String
koreExecSh
    ( KoreExecOptions
        _
        patternFileName
        outputFileName
        mainModuleName
        (TimeOut timeout)
        smtPrelude
        smtSolver
        breadthLimit
        depthLimit
        strategy
        koreLogOptions
        koreSearchOptions
        koreProveOptions
        koreMergeOptions
        rtsStatistics
        _
    )
  =
    unlines $
        [ "#!/bin/sh"
        , "exec kore-exec \\"
        ]
        <> (fmap (<> " \\") . filter (not . null)) options
  where
    options =
        [ if isJust koreProveOptions then "vdefinition.kore"
            else "definition.kore"
        , if isJust patternFileName then "--pattern pgm.kore" else ""
        , if isJust outputFileName then "--output result.kore" else ""
        , "--module " <> unpack (getModuleName mainModuleName)
        , maybeLimit "" (("--smt-timeout " <>) . show) timeout
        , maybe "" ("--smt-prelude " <>) smtPrelude
        , "--smt " <> fmap Char.toLower (show smtSolver)
        , maybeLimit "" (("--breadth " <>) . show) breadthLimit
        , maybeLimit "" (("--depth " <>) . show) depthLimit
        , "--strategy " <> fst strategy
        ]
        <> unparseKoreLogOptions koreLogOptions
        <> maybe mempty unparseKoreSearchOptions koreSearchOptions
        <> maybe mempty unparseKoreProveOptions koreProveOptions
        <> maybe mempty unparseKoreMergeOptions koreMergeOptions
        <> maybe mempty ((:[]) . ("--rts-statistics " <>)) rtsStatistics

writeKoreSearchFiles :: FilePath -> KoreSearchOptions -> IO ()
writeKoreSearchFiles reportFile KoreSearchOptions { searchFileName } =
    copyFile searchFileName $ reportFile <> "/searchFile.kore"

writeKoreMergeFiles :: FilePath -> KoreMergeOptions -> IO ()
writeKoreMergeFiles reportFile KoreMergeOptions { rulesFileName } =
    copyFile rulesFileName $ reportFile <> "/mergeRules.kore"

writeKoreProveFiles :: FilePath -> KoreProveOptions -> IO ()
writeKoreProveFiles reportFile koreProveOptions = do
    let KoreProveOptions { specFileName } = koreProveOptions
    copyFile specFileName (reportFile </> "spec.kore")
    let KoreProveOptions { saveProofs } = koreProveOptions
    Foldable.forM_ saveProofs $ \filePath ->
        Monad.whenM
            (doesFileExist filePath)
            (copyFile filePath (reportFile </> "save-proofs.kore"))

writeOptionsAndKoreFiles :: FilePath -> KoreExecOptions -> IO ()
writeOptionsAndKoreFiles
    reportDirectory
    opts@KoreExecOptions
        { definitionFileName
        , patternFileName
        , koreSearchOptions
        , koreProveOptions
        , koreMergeOptions
        }
  = do
    let shellScript = reportDirectory </> "kore-exec.sh"
    writeFile shellScript
        . koreExecSh
        $ opts
    let allPermissions =
            setOwnerReadable True
            . setOwnerWritable True
            . setOwnerExecutable True
            . setOwnerSearchable True
    setPermissions shellScript $ allPermissions emptyPermissions
    copyFile
        definitionFileName
        (  reportDirectory
        </> if isJust koreProveOptions
            then "vdefinition.kore"
            else "definition.kore"
        )
    Foldable.forM_ patternFileName
        $ flip copyFile (reportDirectory </> "pgm.kore")
    Foldable.forM_
        koreSearchOptions
        (writeKoreSearchFiles reportDirectory)
    Foldable.forM_
        koreMergeOptions
        (writeKoreMergeFiles reportDirectory)
    Foldable.forM_
        koreProveOptions
        (writeKoreProveFiles reportDirectory)

-- TODO(virgil): Maybe add a regression test for main.
-- | Loads a kore definition file and uses it to execute kore programs
main :: IO ()
main = do
    options <-
        mainGlobal (ExeName "kore-exec") parseKoreExecOptions parserInfoModifiers
    Foldable.forM_ (localOptions options) mainWithOptions

mainWithOptions :: KoreExecOptions -> IO ()
mainWithOptions execOptions = do
    let KoreExecOptions { koreLogOptions, bugReport } = execOptions
    exitCode <-
        withBugReport bugReport $ \tmpDir -> do
            writeOptionsAndKoreFiles tmpDir execOptions
            go
                & handle handleWithConfiguration
                & handle handleSomeEntry
                & handle (handleSomeException tmpDir)
                & runKoreLog tmpDir koreLogOptions
    let KoreExecOptions { rtsStatistics } = execOptions
    Foldable.forM_ rtsStatistics $ \filePath ->
        writeStats filePath =<< getStats
    exitWith exitCode
  where
    KoreExecOptions { koreProveOptions } = execOptions
    KoreExecOptions { koreSearchOptions } = execOptions
    KoreExecOptions { koreMergeOptions } = execOptions

    handleSomeEntry
        :: SomeEntry -> Main ExitCode
    handleSomeEntry (SomeEntry entry) = do
        logEntry entry
        return $ ExitFailure 1

    handleSomeException :: FilePath -> SomeException -> Main ExitCode
    handleSomeException tempDirectory someException = do
        errorException someException
        lift
            $ writeFile
                (tempDirectory <> "/error.log")
                (displayException someException)
        return $ ExitFailure 1

    handleWithConfiguration :: Goal.WithConfiguration -> Main ExitCode
    handleWithConfiguration
        (Goal.WithConfiguration lastConfiguration someException)
      = do
        liftIO $ renderResult
            execOptions
            ("// Last configuration:\n" <> unparse lastConfiguration)
        throwM someException

    go :: Main ExitCode
    go
      | Just proveOptions@KoreProveOptions{bmc} <- koreProveOptions =
        if bmc
            then koreBmc execOptions proveOptions
            else koreProve execOptions proveOptions

      | Just searchOptions <- koreSearchOptions =
        koreSearch execOptions searchOptions

      | Just mergeOptions <- koreMergeOptions =
        koreMerge execOptions mergeOptions

      | otherwise =
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
    final <-
        execute execOptions mainModule
        $ search breadthLimit mainModule strategy' initial target config
    lift $ renderResult execOptions (unparse final)
    return ExitSuccess
  where
    KoreSearchOptions { bound, searchType } = searchOptions
    config = Search.Config { bound, searchType }
    KoreExecOptions { breadthLimit, depthLimit, strategy } = execOptions
    strategy' = Limit.replicate depthLimit . snd strategy

koreRun :: KoreExecOptions -> Main ExitCode
koreRun execOptions = do
    let KoreExecOptions { definitionFileName } = execOptions
    definition <- loadDefinitions [definitionFileName]
    let KoreExecOptions { mainModuleName } = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreExecOptions { patternFileName } = execOptions
    initial <- loadPattern mainModule patternFileName
    (exitCode, final) <- execute execOptions mainModule $ do
        final <- exec breadthLimit mainModule strategy' initial
        exitCode <- execGetExitCode mainModule strategy' final
        return (exitCode, final)
    lift $ renderResult execOptions (unparse final)
    return exitCode
  where
    KoreExecOptions { breadthLimit, depthLimit, strategy } = execOptions
    strategy' = Limit.replicate depthLimit . snd strategy

koreProve :: KoreExecOptions -> KoreProveOptions -> Main ExitCode
koreProve execOptions proveOptions = do
    let KoreExecOptions { definitionFileName } = execOptions
        KoreProveOptions { specFileName } = proveOptions
    definition <- loadDefinitions [definitionFileName, specFileName]
    let KoreExecOptions { mainModuleName } = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreProveOptions { specMainModule } = proveOptions
    specModule <- loadModule specMainModule definition
    let KoreProveOptions { saveProofs } = proveOptions
    maybeAlreadyProvenModule <- loadProven definitionFileName saveProofs
    proveResult <- execute execOptions mainModule $ do
        let KoreExecOptions { breadthLimit, depthLimit } = execOptions
            KoreProveOptions { graphSearch } = proveOptions
        prove
            graphSearch
            breadthLimit
            depthLimit
            mainModule
            specModule
            maybeAlreadyProvenModule

    (exitCode, final) <- case proveResult of
        Left Stuck { stuckPattern, provenClaims } -> do
            maybe
                (return ())
                (lift . saveProven specModule provenClaims)
                saveProofs
            return (failure $ Pattern.toTermLike stuckPattern)
        Right () -> return success

    lift $ renderResult execOptions (unparse final)
    return exitCode
  where
    failure pat = (ExitFailure 1, pat)
    success :: (ExitCode, TermLike VariableName)
    success = (ExitSuccess, mkTop $ mkSortVariable "R")

    loadProven
        :: FilePath
        -> Maybe FilePath
        -> Main (Maybe (VerifiedModule StepperAttributes))
    loadProven _ Nothing = return Nothing
    loadProven definitionFileName (Just saveProofsFileName) = do
        fileExists <- lift $ doesFileExist saveProofsFileName
        if fileExists
            then do
                savedProofsDefinition <-
                    loadDefinitions [definitionFileName, saveProofsFileName]
                savedProofsModule <-
                    loadModule savedProofsModuleName savedProofsDefinition
                return (Just savedProofsModule)
            else return Nothing

    saveProven
        :: VerifiedModule StepperAttributes
        -> [ReachabilityRule]
        -> FilePath
        -> IO ()
    saveProven specModule provenClaims outputFile =
        withFile outputFile WriteMode
            (`hPutDoc` unparse provenDefinition)
      where
        specModuleDefinitions :: [Sentence (TermLike VariableName)]
        specModuleDefinitions =
            filter isNotAxiomOrClaim (indexedModuleRawSentences specModule)

        isNotAxiomOrClaim :: Sentence patternType -> Bool
        isNotAxiomOrClaim (SentenceAxiomSentence  _) = False
        isNotAxiomOrClaim (SentenceClaimSentence _) = False
        isNotAxiomOrClaim (SentenceAliasSentence _) = True
        isNotAxiomOrClaim (SentenceSymbolSentence _) = True
        isNotAxiomOrClaim (SentenceImportSentence _) = True
        isNotAxiomOrClaim (SentenceSortSentence _) = True
        isNotAxiomOrClaim (SentenceHookSentence _) = True

        provenModule =
            Module
                { moduleName = savedProofsModuleName
                , moduleSentences =
                    specModuleDefinitions ++ map Rule.toSentence provenClaims
                , moduleAttributes = def
                }
        provenDefinition = Definition
            { definitionAttributes = def
            , definitionModules = [provenModule]
            }

koreBmc :: KoreExecOptions -> KoreProveOptions -> Main ExitCode
koreBmc execOptions proveOptions = do
    let KoreExecOptions { definitionFileName } = execOptions
        KoreProveOptions { specFileName } = proveOptions
    definition <- loadDefinitions [definitionFileName, specFileName]
    let KoreExecOptions { mainModuleName } = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreProveOptions { specMainModule } = proveOptions
    specModule <- loadModule specMainModule definition
    (exitCode, final) <- execute execOptions mainModule $ do
        let KoreExecOptions { breadthLimit, depthLimit } = execOptions
            KoreProveOptions { graphSearch } = proveOptions
        checkResult <-
            boundedModelCheck
                breadthLimit
                depthLimit
                mainModule
                specModule
                graphSearch
        case checkResult of
            Bounded.Proved -> return success
            Bounded.Unknown -> return unknown
            Bounded.Failed final -> return (failure final)
    lift $ renderResult execOptions (unparse final)
    return exitCode
  where
    failure pat = (ExitFailure 1, pat)
    success = (ExitSuccess, mkTop $ mkSortVariable "R")
    unknown =
        ( ExitSuccess
        , mkElemVar $ mkElementVariable "Unknown" (mkSort $ noLocationId "SortUnknown")
        )

koreMerge :: KoreExecOptions -> KoreMergeOptions -> Main ExitCode
koreMerge execOptions mergeOptions = do
    let KoreExecOptions {definitionFileName} = execOptions
    definition <- loadDefinitions [definitionFileName]
    let KoreExecOptions {mainModuleName} = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreMergeOptions {rulesFileName} = mergeOptions
    ruleIds <- lift $ loadRuleIds rulesFileName
    let KoreMergeOptions {maybeBatchSize} = mergeOptions
    eitherMergedRule <- execute execOptions mainModule $
        case maybeBatchSize of
            Just batchSize ->
                mergeRulesConsecutiveBatches batchSize mainModule ruleIds
            Nothing -> mergeAllRules mainModule ruleIds
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
    , WithLog LogMessage exe
    )

-- | Run the worker in the context of the main module.
execute
    :: forall r
    .  KoreExecOptions
    -> LoadedModule  -- ^ Main module
    -> (forall exe. MonadExecute exe => exe r)  -- ^ Worker
    -> Main r
execute options mainModule worker =
    clockSomethingIO "Executing"
        $ case smtSolver of
            Z3   -> withZ3
            None -> withoutSMT
  where
    withZ3 =
        SMT.runSMT config $ do
            give (MetadataTools.build mainModule) (declareSMTLemmas mainModule)
            worker
    withoutSMT = SMT.runNoSMT worker
    KoreExecOptions { smtTimeOut, smtPrelude, smtSolver } = options
    config =
        SMT.defaultConfig
            { SMT.timeOut = smtTimeOut
            , SMT.preludeFile = smtPrelude
            }

loadPattern :: LoadedModule -> Maybe FilePath -> Main (TermLike VariableName)
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
-- converts it to a pure pattern, and prints timing information.
mainPatternParseAndVerify
    :: VerifiedModule StepperAttributes
    -> String
    -> Main (TermLike VariableName)
mainPatternParseAndVerify indexedModule patternFileName =
    mainPatternParse patternFileName >>= mainPatternVerify indexedModule

mainParseSearchPattern
    :: VerifiedModule StepperAttributes
    -> String
    -> Main (Pattern VariableName)
mainParseSearchPattern indexedModule patternFileName = do
    purePattern <- mainPatternParseAndVerify indexedModule patternFileName
    case purePattern of
        And_ _ term predicateTerm -> return
            Conditional
                { term
                , predicate =
                    either (error . show . pretty) id
                        (makePredicate predicateTerm)
                , substitution = mempty
                }
        _ -> error "Unexpected non-conjunctive pattern"

savedProofsModuleName :: ModuleName
savedProofsModuleName = ModuleName
    "haskell-backend-saved-claims-43943e50-f723-47cd-99fd-07104d664c6d"
