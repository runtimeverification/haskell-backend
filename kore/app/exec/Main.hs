module Main (main) where

import Control.Lens qualified as Lens
import Control.Monad.Catch (
    MonadMask,
    handle,
    throwM,
 )
import Control.Monad.Extra as Monad
import Data.ByteString qualified as ByteString
import Data.Default (
    def,
 )
import Data.Generics.Product (
    field,
 )
import Data.Limit (
    Limit (..),
    maybeLimit,
 )
import Data.List (
    intercalate,
 )
import Data.Map.Strict (
    Map,
 )
import Data.Reflection
import Data.Serialize
import Data.Serialize qualified as Serialize
import Data.Text (
    unpack,
 )
import GHC.Generics qualified as GHC
import GlobalMain
import Kore.Attribute.Definition (
    KFileLocations (..),
 )
import Kore.Attribute.Symbol as Attribute
import Kore.BugReport
import Kore.Equation (
    Equation,
 )
import Kore.Exec
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
    VerifiedModuleSyntax,
    indexedModuleRawSentences,
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.IndexedModule.MetadataToolsBuilder qualified as MetadataTools (
    build,
 )
import Kore.IndexedModule.OverloadGraph
import Kore.IndexedModule.SortGraph
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.TermLike (
    TermLike,
    VariableName,
    mkSortVariable,
    mkTop,
 )
import Kore.Log (
    KoreLogOptions (..),
    LogMessage,
    WithLog,
    parseKoreLogOptions,
    runKoreLog,
    unparseKoreLogOptions,
 )
import Kore.Log.ErrorParse (
    errorParse,
 )
import Kore.Log.ErrorException (
    handleSomeException,
 )
import Kore.Log.WarnBoundedModelChecker (
    warnBoundedModelChecker,
 )
import Kore.Log.WarnIfLowProductivity (
    warnIfLowProductivity,
 )
import Kore.ModelChecker.Bounded qualified as Bounded (
    CheckResult (..),
 )
import Kore.Parser.ParserUtils (
    readPositiveIntegral,
 )
import Kore.Reachability (
    ProveClaimsResult (..),
    SomeClaim,
    StuckClaim (..),
    getConfiguration,
    lensClaimPattern,
 )
import Kore.Reachability.Claim qualified as Claim
import Kore.Rewrite
import Kore.Rewrite.Axiom.Identifier (
    AxiomIdentifier,
 )
import Kore.Rewrite.ClaimPattern (
    getClaimPatternSort,
 )
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.SMT.Lemma
import Kore.Rewrite.Search (
    SearchType (..),
 )
import Kore.Rewrite.Search qualified as Search
import Kore.Rewrite.Strategy (
    GraphSearchOrder (..),
 )
import Kore.Syntax.Definition (
    Definition (Definition),
    Module (Module),
    ModuleName (..),
    Sentence (..),
    SentenceAxiom (..),
 )
import Kore.Syntax.Definition qualified as Definition.DoNotUse
import Kore.Unparser (
    unparse,
 )
import Options.Applicative (
    InfoMod,
    Parser,
    argument,
    auto,
    fullDesc,
    header,
    help,
    long,
    metavar,
    option,
    progDesc,
    readerError,
    str,
    strOption,
    value,
 )
import Options.Applicative qualified as Options
import Options.Applicative.Help.Pretty qualified as OptPretty
import Options.SMT (
    KoreSolverOptions (..),
    Solver (..),
    ensureSmtPreludeExists,
    parseKoreSolverOptions,
    unparseKoreSolverOptions,
    writeKoreSolverFiles,
 )
import Prelude.Kore
import Pretty (
    Doc,
    hPutDoc,
    putDoc,
 )
import Prof (
    MonadProf,
 )
import SMT (
    MonadSMT,
 )
import SMT qualified
import Stats
import System.Clock (
    Clock (Monotonic),
    TimeSpec,
    getTime,
 )
import System.Directory (
    copyFile,
    doesFileExist,
    emptyPermissions,
    setOwnerExecutable,
    setOwnerReadable,
    setOwnerSearchable,
    setOwnerWritable,
    setPermissions,
 )
import System.Exit (
    exitWith,
 )
import System.FilePath (
    (</>),
 )
import System.IO (
    IOMode (WriteMode),
    withFile,
 )

{-
Main module to run kore-exec
TODO: add command line argument tab-completion
-}

data KoreSearchOptions = KoreSearchOptions
    { -- | Name of file containing a pattern to match during execution
      searchFileName :: !FilePath
    , -- | The maximum bound on the number of search matches
      bound :: !(Limit Natural)
    , -- | The type of search to perform
      searchType :: !SearchType
    }
    deriving stock (GHC.Generic)

parseKoreSearchOptions :: Parser KoreSearchOptions
parseKoreSearchOptions =
    KoreSearchOptions
        <$> strOption
            ( metavar "SEARCH_FILE"
                <> long "search"
                <> help
                    "Kore source file representing pattern to search for. \
                    \Needs --module."
            )
        <*> parseBound
        <*> parseSearchType
  where
    parseBound = Limit <$> bound <|> pure Unlimited
    bound =
        option
            auto
            ( metavar "BOUND"
                <> long "bound"
                <> help "Maximum number of solutions."
            )
    parseSearchType =
        parseSum
            "SEARCH_TYPE"
            "searchType"
            "Search type (selects potential solutions)"
            (map (\s -> (show s, s)) [ONE, FINAL, STAR, PLUS])

parseSum :: String -> String -> String -> [(String, value)] -> Parser value
parseSum metaName longName helpMsg options =
    option
        (snd <$> readSum longName options)
        ( metavar metaName
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

applyKoreSearchOptions ::
    Maybe KoreSearchOptions ->
    KoreExecOptions ->
    KoreExecOptions
applyKoreSearchOptions Nothing koreExecOpts = koreExecOpts
applyKoreSearchOptions koreSearchOptions@(Just koreSearchOpts) koreExecOpts =
    koreExecOpts
        { koreSearchOptions
        , depthLimit = min depthLimit searchTypeDepthLimit
        }
  where
    KoreSearchOptions{searchType} = koreSearchOpts
    KoreExecOptions{depthLimit} = koreExecOpts
    searchTypeDepthLimit =
        case searchType of
            ONE -> Limit 1
            _ -> Unlimited

-- | Main options record
data KoreExecOptions = KoreExecOptions
    { -- | Name for a file containing a definition to verify and use for execution
      definitionFileName :: !FilePath
    , -- | Name for file containing a pattern to verify and use for execution
      patternFileName :: !(Maybe FilePath)
    , -- | Name for file to contain the output pattern
      outputFileName :: !(Maybe FilePath)
    , -- | The name of the main module in the definition
      mainModuleName :: !ModuleName
    , breadthLimit :: !(Limit Natural)
    , depthLimit :: !(Limit Natural)
    , strategy :: !ExecutionMode
    , koreSolverOptions :: !KoreSolverOptions
    , koreLogOptions :: !KoreLogOptions
    , koreSearchOptions :: !(Maybe KoreSearchOptions)
    , koreProveOptions :: !(Maybe KoreProveOptions)
    , rtsStatistics :: !(Maybe FilePath)
    , bugReportOption :: !BugReportOption
    , maxCounterexamples :: Natural
    }
    deriving stock (GHC.Generic)

-- | Command Line Argument Parser
parseKoreExecOptions :: TimeSpec -> Parser KoreExecOptions
parseKoreExecOptions startTime =
    applyKoreSearchOptions
        <$> optional parseKoreSearchOptions
        <*> parseKoreExecOptions0
  where
    parseKoreExecOptions0 :: Parser KoreExecOptions
    parseKoreExecOptions0 =
        KoreExecOptions
            <$> argument
                str
                ( metavar "DEFINITION_FILE"
                    <> help "Kore definition file to verify and use for execution"
                )
            <*> optional
                ( strOption
                    ( metavar "PATTERN_FILE"
                        <> long "pattern"
                        <> help
                            "Verify and execute the Kore pattern found in PATTERN_FILE."
                    )
                )
            <*> optional
                ( strOption
                    ( metavar "PATTERN_OUTPUT_FILE"
                        <> long "output"
                        <> help "Output file to contain final Kore pattern."
                    )
                )
            <*> parseMainModuleName
            <*> parseBreadthLimit
            <*> parseDepthLimit
            <*> parseStrategy
            <*> parseKoreSolverOptions
            <*> parseKoreLogOptions (ExeName "kore-exec") startTime
            <*> pure Nothing
            <*> optional parseKoreProveOptions
            <*> optional parseRtsStatistics
            <*> parseBugReportOption
            <*> parseMaxCounterexamples
    parseMaxCounterexamples = counterexamples <|> pure 1
      where
        counterexamples =
            option
                (readPositiveIntegral id "max-counterexamples")
                ( metavar "MAX_COUNTEREXAMPLES"
                    <> long "max-counterexamples"
                    <> help "Specify the maximum number of counterexamples."
                )
    parseBreadthLimit = Limit <$> breadth <|> pure Unlimited
    parseDepthLimit = Limit <$> depth <|> pure Unlimited
    parseStrategy =
        option
            parseExecutionMode
            ( metavar "STRATEGY"
                <> long "strategy"
                <> value All
                <> help "Select rewrites using STRATEGY."
            )

    breadth =
        option
            auto
            ( metavar "BREADTH"
                <> long "breadth"
                <> help "Allow up to BREADTH parallel execution branches."
            )
    depth =
        option
            auto
            ( metavar "DEPTH"
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
    parseExecutionMode = do
        val <- str
        case val :: String of
            "all" -> return All
            "any" -> return Any
            _ ->
                readerError $
                    show $
                        OptPretty.hsep
                            [ "Unknown option"
                            , OptPretty.squotes (OptPretty.text val)
                                <> OptPretty.dot
                            , "Known options are 'all' and 'any'."
                            ]

-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> progDesc
            "Uses Kore definition in DEFINITION_FILE to execute pattern \
            \in PATTERN_FILE."
        <> header "kore-exec - an interpreter for Kore definitions"

unparseKoreSearchOptions :: KoreSearchOptions -> [String]
unparseKoreSearchOptions (KoreSearchOptions _ bound searchType) =
    [ "--search searchFile.kore"
    , maybeLimit "" (\limit -> unwords ["--bound", show limit]) bound
    , unwords ["--searchType", show searchType]
    ]

unparseKoreProveOptions :: KoreProveOptions -> [String]
unparseKoreProveOptions
    ( KoreProveOptions
            _
            (ModuleName moduleName)
            graphSearch
            bmc
            saveProofs
        ) =
        [ "--prove spec.kore"
        , unwords ["--spec-module", unpack moduleName]
        , unwords
            [ "--graph-search"
            , if graphSearch == DepthFirst then "depth-first" else "breadth-first"
            ]
        , if bmc then "--bmc" else ""
        , maybe "" ("--save-proofs " <>) saveProofs
        ]

koreExecSh :: KoreExecOptions -> String
koreExecSh
    koreExecOptions@( KoreExecOptions
                            _
                            patternFileName
                            outputFileName
                            mainModuleName
                            breadthLimit
                            depthLimit
                            strategy
                            koreSolverOptions
                            koreLogOptions
                            koreSearchOptions
                            koreProveOptions
                            rtsStatistics
                            _
                            maxCounterexamples
                        ) =
        unlines $
            [ "#!/bin/sh"
            , "exec kore-exec \\"
            ]
                <> fmap (\line -> "    " <> line <> " \\") options
                <> ["    \"$@\""]
      where
        options =
            concat
                [ catMaybes
                    [ pure $ defaultDefinitionFilePath koreExecOptions
                    , patternFileName $> "--pattern pgm.kore"
                    , outputFileName $> "--output result.kore"
                    , pure $ unwords ["--module", unpack (getModuleName mainModuleName)]
                    , (\limit -> unwords ["--breadth", show limit])
                        <$> maybeLimit Nothing Just breadthLimit
                    , (\limit -> unwords ["--depth", show limit])
                        <$> maybeLimit Nothing Just depthLimit
                    , pure $ unwords ["--strategy", unparseExecutionMode strategy]
                    , rtsStatistics
                        $> unwords ["--rts-statistics", defaultRtsStatisticsFilePath]
                    , pure $ unwords ["--max-counterexamples", show maxCounterexamples]
                    ]
                , unparseKoreSolverOptions koreSolverOptions
                , unparseKoreLogOptions koreLogOptions
                , maybe mempty unparseKoreSearchOptions koreSearchOptions
                , maybe mempty unparseKoreProveOptions koreProveOptions
                ]
        unparseExecutionMode All = "all"
        unparseExecutionMode Any = "any"

defaultDefinitionFilePath :: KoreExecOptions -> FilePath
defaultDefinitionFilePath KoreExecOptions{koreProveOptions}
    | isJust koreProveOptions = "vdefinition.kore"
    | otherwise = "definition.kore"

defaultRtsStatisticsFilePath :: FilePath
defaultRtsStatisticsFilePath = "rts-statistics.json"

writeKoreSearchFiles :: FilePath -> KoreSearchOptions -> IO ()
writeKoreSearchFiles reportFile KoreSearchOptions{searchFileName} =
    copyFile searchFileName $ reportFile <> "/searchFile.kore"

writeKoreProveFiles :: FilePath -> KoreProveOptions -> IO ()
writeKoreProveFiles reportFile koreProveOptions = do
    let KoreProveOptions{specFileName} = koreProveOptions
    copyFile specFileName (reportFile </> "spec.kore")
    let KoreProveOptions{saveProofs} = koreProveOptions
    for_ saveProofs $ \filePath ->
        Monad.whenM
            (doesFileExist filePath)
            (copyFile filePath (reportFile </> "save-proofs.kore"))

writeOptionsAndKoreFiles :: FilePath -> KoreExecOptions -> IO ()
writeOptionsAndKoreFiles
    reportDirectory
    opts@KoreExecOptions
        { definitionFileName
        , patternFileName
        , koreSolverOptions
        , koreSearchOptions
        , koreProveOptions
        } =
        do
            let shellScript = reportDirectory </> "kore-exec.sh"
            writeFile shellScript . koreExecSh $ opts
            let allPermissions =
                    setOwnerReadable True
                        . setOwnerWritable True
                        . setOwnerExecutable True
                        . setOwnerSearchable True
            setPermissions shellScript $ allPermissions emptyPermissions
            copyFile
                definitionFileName
                (reportDirectory </> defaultDefinitionFilePath opts)
            for_ patternFileName $
                flip copyFile (reportDirectory </> "pgm.kore")
            writeKoreSolverFiles koreSolverOptions reportDirectory
            for_
                koreSearchOptions
                (writeKoreSearchFiles reportDirectory)
            for_
                koreProveOptions
                (writeKoreProveFiles reportDirectory)

exeName :: ExeName
exeName = ExeName "kore-exec"

-- | Environment variable name for extra arguments
envName :: String
envName = "KORE_EXEC_OPTS"

-- TODO(virgil): Maybe add a regression test for main.

-- | Loads a kore definition file and uses it to execute kore programs
main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <-
        mainGlobal
            Main.exeName
            (Just envName)
            (parseKoreExecOptions startTime)
            parserInfoModifiers
    for_ (localOptions options) mainWithOptions

{- | Use the parsed 'KoreExecOptions' to set up output and logging, then
dispatch the requested command.
-}
mainWithOptions :: LocalOptions KoreExecOptions -> IO ()
mainWithOptions LocalOptions{execOptions, simplifierx} = do
    let KoreExecOptions{koreSolverOptions, bugReportOption, outputFileName} =
            execOptions
    ensureSmtPreludeExists koreSolverOptions
    exitCode <-
        withBugReport Main.exeName bugReportOption $ \tmpDir -> do
            let execOptions' =
                    execOptions
                        { outputFileName = Just (tmpDir </> "result.kore")
                        }
            writeOptionsAndKoreFiles tmpDir execOptions'
            e <-
                mainDispatch LocalOptions{execOptions = execOptions', simplifierx}
                    & handle handleWithConfiguration
                    & handle handleSomeException
                    & runKoreLog tmpDir koreLogOptions
            case outputFileName of
                Nothing -> readFile (tmpDir </> "result.kore") >>= putStr
                Just fileName -> copyFile (tmpDir </> "result.kore") fileName
            return e
    let KoreExecOptions{rtsStatistics} = execOptions
    for_ rtsStatistics $ \filePath ->
        writeStats filePath =<< getStats
    exitWith exitCode
  where
    KoreExecOptions{koreLogOptions} = execOptions

    handleWithConfiguration :: Claim.WithConfiguration -> Main ExitCode
    handleWithConfiguration
        (Claim.WithConfiguration lastConfiguration someException) =
            do
                liftIO $
                    renderResult
                        execOptions
                        ("// Last configuration:\n" <> unparse lastConfiguration)
                throwM someException

-- | Dispatch the requested command, for example 'koreProve' or 'koreRun'.
mainDispatch :: LocalOptions KoreExecOptions -> Main ExitCode
mainDispatch = warnProductivity . mainDispatchWorker
  where
    warnProductivity :: Main (KFileLocations, ExitCode) -> Main ExitCode
    warnProductivity action = do
        (kFileLocations, exitCode) <- action
        warnIfLowProductivity kFileLocations
        return exitCode
    mainDispatchWorker ::
        LocalOptions KoreExecOptions ->
        Main (KFileLocations, ExitCode)
    mainDispatchWorker localOptions@LocalOptions{execOptions}
        | Just proveOptions@KoreProveOptions{bmc} <- koreProveOptions =
            if bmc
                then koreBmc localOptions proveOptions
                else koreProve localOptions proveOptions
        | Just searchOptions <- koreSearchOptions =
            koreSearch localOptions searchOptions
        | otherwise =
            koreRun localOptions
      where
        KoreExecOptions{koreProveOptions} = execOptions
        KoreExecOptions{koreSearchOptions} = execOptions


data SerializedDefinition = SerializedDefinition
        [SentenceAxiom (TermLike VariableName)]
        SortGraph
        OverloadGraph
        (SmtMetadataTools StepperAttributes)
        (VerifiedModuleSyntax StepperAttributes)
        KFileLocations
        Initialized
        (Map AxiomIdentifier [Equation VariableName])
   deriving stock (GHC.Generic)
   deriving anyclass Serialize

deserializeDefinition ::
    FilePath ->
    Main SerializedDefinition
deserializeDefinition definitionFilePath = do
    bytes <- ByteString.readFile definitionFilePath & liftIO
    let result = Serialize.decode bytes
    either errorParse return result

koreSearch ::
    LocalOptions KoreExecOptions ->
    KoreSearchOptions ->
    Main (KFileLocations, ExitCode)
koreSearch LocalOptions{execOptions, simplifierx} searchOptions = do
    let KoreExecOptions{definitionFileName} = execOptions
    SerializedDefinition lemmas sorts overloads metadataTools syntax locations rewrites equations <- deserializeDefinition definitionFileName
    let KoreSearchOptions{searchFileName} = searchOptions
    target <- mainParseSearchPattern syntax searchFileName
    let KoreExecOptions{patternFileName} = execOptions
    initial <- loadPattern syntax patternFileName
    final <-
        execute execOptions metadataTools lemmas $
            search
                simplifierx
                depthLimit
                breadthLimit
                syntax
                sorts
                overloads
                metadataTools
                equations
                rewrites
                initial
                target
                config
    lift $ renderResult execOptions (unparse final)
    return (locations, ExitSuccess)
  where
    KoreSearchOptions{bound, searchType} = searchOptions
    config = Search.Config{bound, searchType}
    KoreExecOptions{breadthLimit, depthLimit} = execOptions

koreRun :: LocalOptions KoreExecOptions -> Main (KFileLocations, ExitCode)
koreRun LocalOptions{execOptions, simplifierx} = do
    let KoreExecOptions{definitionFileName} = execOptions
    SerializedDefinition lemmas sorts overloads metadataTools syntax locations rewrites equations <- deserializeDefinition definitionFileName
    let KoreExecOptions{patternFileName} = execOptions
    initial <- loadPattern syntax patternFileName
    (exitCode, final) <-
        execute execOptions metadataTools lemmas $
            exec
                simplifierx
                depthLimit
                breadthLimit
                syntax
                sorts
                overloads
                metadataTools
                equations
                rewrites
                strategy
                initial
    lift $ renderResult execOptions (unparse final)
    return (locations, exitCode)
  where
    KoreExecOptions{breadthLimit, depthLimit, strategy} = execOptions

koreProve ::
    LocalOptions KoreExecOptions ->
    KoreProveOptions ->
    Main (KFileLocations, ExitCode)
koreProve LocalOptions{execOptions, simplifierx} proveOptions = do
    let KoreExecOptions{definitionFileName} = execOptions
        KoreProveOptions{specFileName} = proveOptions
    definition <- loadDefinitions [definitionFileName, specFileName]
    let KoreExecOptions{mainModuleName} = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreProveOptions{specMainModule} = proveOptions
    specModule <- loadModule specMainModule definition
    let mainModule' = addExtraAxioms mainModule specModule
    let KoreProveOptions{saveProofs} = proveOptions
    maybeAlreadyProvenModule <- loadProven definitionFileName saveProofs
    let KoreExecOptions{maxCounterexamples} = execOptions
    proveResult <- execute execOptions (MetadataTools.build mainModule) (getSMTLemmas mainModule) $ do
        let KoreExecOptions{breadthLimit, depthLimit} = execOptions
            KoreProveOptions{graphSearch} = proveOptions
        prove
            simplifierx
            graphSearch
            breadthLimit
            depthLimit
            maxCounterexamples
            mainModule'
            specModule
            maybeAlreadyProvenModule

    let ProveClaimsResult{stuckClaims, provenClaims} = proveResult
    let (exitCode, final) =
            case foldFirst stuckClaims of
                Nothing -> success -- stuckClaims is empty
                Just claim ->
                    stuckPatterns
                        & OrPattern.toTermLike (getClaimPatternSort $ claimPattern claim)
                        & failure
          where
            stuckPatterns =
                OrPattern.fromPatterns (MultiAnd.map getStuckConfig stuckClaims)
            getStuckConfig =
                getRewritingPattern . getConfiguration . getStuckClaim
            claimPattern claim =
                claim
                    & getStuckClaim
                    & Lens.view lensClaimPattern
    lift $ for_ saveProofs $ saveProven specModule provenClaims
    lift $ renderResult execOptions (unparse final)
    return (kFileLocations definition, exitCode)
  where
    failure pat = (ExitFailure 1, pat)
    success :: (ExitCode, TermLike VariableName)
    success = (ExitSuccess, mkTop $ mkSortVariable "R")

    loadProven ::
        FilePath ->
        Maybe FilePath ->
        Main (Maybe (VerifiedModule StepperAttributes))
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

    saveProven ::
        VerifiedModule StepperAttributes ->
        MultiAnd SomeClaim ->
        FilePath ->
        IO ()
    saveProven specModule (toList -> provenClaims) outputFile =
        withFile
            outputFile
            WriteMode
            (`hPutDoc` unparse provenDefinition)
      where
        specModuleDefinitions :: [Sentence (TermLike VariableName)]
        specModuleDefinitions =
            filter isNotAxiomOrClaim (indexedModuleRawSentences specModule)

        isNotAxiomOrClaim :: Sentence patternType -> Bool
        isNotAxiomOrClaim (SentenceAxiomSentence _) = False
        isNotAxiomOrClaim (SentenceClaimSentence _) = False
        isNotAxiomOrClaim (SentenceAliasSentence _) = True
        isNotAxiomOrClaim (SentenceSymbolSentence _) = True
        isNotAxiomOrClaim (SentenceImportSentence _) = True
        isNotAxiomOrClaim (SentenceSortSentence _) = True
        isNotAxiomOrClaim (SentenceHookSentence _) = True

        provenClaimSentences = map (from @SomeClaim @(Sentence _)) provenClaims
        provenModule =
            Module
                { moduleName = savedProofsModuleName
                , moduleSentences =
                    specModuleDefinitions <> provenClaimSentences
                , moduleAttributes = def
                }

        provenDefinition =
            Definition
                { definitionAttributes = def
                , definitionModules = [provenModule]
                }

koreBmc ::
    LocalOptions KoreExecOptions ->
    KoreProveOptions ->
    Main (KFileLocations, ExitCode)
koreBmc LocalOptions{execOptions, simplifierx} proveOptions = do
    let KoreExecOptions{definitionFileName} = execOptions
        KoreProveOptions{specFileName} = proveOptions
    definition <- loadDefinitions [definitionFileName, specFileName]
    let KoreExecOptions{mainModuleName} = execOptions
    mainModule <- loadModule mainModuleName definition
    let KoreProveOptions{specMainModule} = proveOptions
    specModule <- loadModule specMainModule definition
    (exitCode, final) <- execute execOptions (MetadataTools.build mainModule) (getSMTLemmas mainModule) $ do
        let KoreExecOptions{breadthLimit, depthLimit} = execOptions
            KoreProveOptions{graphSearch} = proveOptions
        checkResult <-
            boundedModelCheck
                simplifierx
                breadthLimit
                depthLimit
                mainModule
                specModule
                graphSearch
        case checkResult of
            Bounded.Proved -> return success
            Bounded.Unknown claim -> do
                warnBoundedModelChecker claim
                return success
            Bounded.Failed final -> return (failure final)
    lift $ renderResult execOptions (unparse final)
    return (kFileLocations definition, exitCode)
  where
    failure pat = (ExitFailure 1, pat)
    success = (ExitSuccess, mkTop $ mkSortVariable "R")

type MonadExecute exe =
    ( MonadMask exe
    , MonadIO exe
    , MonadSMT exe
    , MonadProf exe
    , WithLog LogMessage exe
    )

-- | Run the worker in the context of the main module.
execute ::
    forall r.
    KoreExecOptions ->
    -- | SMT Lemmas
    SmtMetadataTools StepperAttributes ->
    [SentenceAxiom (TermLike VariableName)] ->
    -- | Worker
    (forall exe. MonadExecute exe => exe r) ->
    Main r
execute options metadataTools lemmas worker =
    clockSomethingIO "Executing" $
        case solver of
            Z3 -> withZ3
            None -> withoutSMT
  where
    withZ3 =
        SMT.runSMT
            config
            (give metadataTools (declareSMTLemmas lemmas))
            worker
    withoutSMT = SMT.runNoSMT worker
    KoreSolverOptions{timeOut, rLimit, resetInterval, prelude, solver} =
        Lens.view (field @"koreSolverOptions") options
    config =
        SMT.defaultConfig
            { SMT.timeOut = timeOut
            , SMT.rLimit = rLimit
            , SMT.resetInterval = resetInterval
            , SMT.prelude = prelude
            }

loadPattern :: LoadedModuleSyntax -> Maybe FilePath -> Main (TermLike VariableName)
loadPattern mainModule (Just fileName) =
    mainPatternParseAndVerify mainModule fileName
loadPattern _ Nothing = error "Missing: --pattern PATTERN_FILE"

renderResult :: KoreExecOptions -> Doc ann -> IO ()
renderResult KoreExecOptions{outputFileName} doc =
    case outputFileName of
        Nothing -> putDoc doc
        Just outputFile -> withFile outputFile WriteMode (`hPutDoc` doc)

savedProofsModuleName :: ModuleName
savedProofsModuleName =
    ModuleName
        "haskell-backend-saved-claims-43943e50-f723-47cd-99fd-07104d664c6d"
