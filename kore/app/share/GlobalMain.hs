{-# LANGUAGE TemplateHaskell #-}

module GlobalMain (
    MainOptions (..),
    GlobalOptions (..),
    KoreProveOptions (..),
    KoreMergeOptions (..),
    ExeName (..),
    Main,
    parseKoreProveOptions,
    parseKoreMergeOptions,
    mainGlobal,
    clockSomething,
    clockSomethingIO,
    mainPatternVerify,
    parseDefinition,
    parseModuleName,
    verifyDefinitionWithBase,
    mainParse,
    lookupMainModule,
    LoadedDefinition (..),
    LoadedModule,
    loadDefinitions,
    loadModule,
    mainParseSearchPattern,
    mainPatternParseAndVerify,
) where

import Control.Exception (
    evaluate,
 )
import Control.Lens (
    (%~),
 )
import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import Data.List (
    intercalate,
    nub,
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
    pack,
 )
import qualified Data.Text.IO as Text
import Data.Version (
    showVersion,
 )
import GHC.Stack (
    emptyCallStack,
 )
import Kore.ASTVerifier.DefinitionVerifier (
    sortModuleClaims,
    verifyAndIndexDefinitionWithBase,
 )
import Kore.ASTVerifier.PatternVerifier as PatternVerifier
import Kore.Attribute.Definition (
    KFileLocations (..),
    parseKFileAttributes,
 )
import Kore.Attribute.SourceLocation (
    notDefault,
 )
import Kore.Attribute.Symbol (
    StepperAttributes,
 )
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Builtin as Builtin
import Kore.IndexedModule.IndexedModule (
    VerifiedModule,
 )
import Kore.Internal.Conditional (Conditional (..))
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.Predicate (makePredicate)
import Kore.Internal.TermLike (TermLike, pattern And_)
import Kore.Log as Log
import Kore.Log.ErrorParse (
    errorParse,
 )
import Kore.Log.ErrorVerify (
    errorVerify,
 )
import Kore.Parser (
    ParsedPattern,
    parseKoreDefinition,
    parseKorePattern,
 )
import qualified Kore.Parser.Lexer as Lexer
import Kore.Parser.ParserUtils (
    parseOnly,
 )
import Kore.Step.Strategy (
    GraphSearchOrder (..),
 )
import Kore.Syntax hiding (Pattern)
import Kore.Syntax.Definition (
    ModuleName (..),
    ParsedDefinition,
    definitionAttributes,
    getModuleNameForError,
 )
import qualified Kore.Verified as Verified
import Kore.VersionInfo
import Options.Applicative (
    InfoMod,
    Parser,
    ParserHelp (..),
    defaultPrefs,
    execParserPure,
    flag,
    handleParseResult,
    help,
    helper,
    info,
    long,
    maybeReader,
    metavar,
    option,
    overFailure,
    readerError,
    str,
    strOption,
    switch,
    value,
    (<**>),
 )
import qualified Options.Applicative as Options
import Options.Applicative.Help.Chunk (
    Chunk (..),
    vsepChunks,
 )
import qualified Options.Applicative.Help.Pretty as Pretty
import qualified Paths_kore as MetaData (
    version,
 )
import Prelude.Kore
import qualified Pretty as KorePretty
import System.Clock (
    Clock (Monotonic),
    diffTimeSpec,
    getTime,
 )
import qualified System.Environment as Env
import qualified Text.Megaparsec as Parser
import Text.Read (
    readMaybe,
 )

type Main = LoggerT IO

data KoreProveOptions = KoreProveOptions
    { -- | Name of file containing the spec to be proven
      specFileName :: !FilePath
    , -- | The main module of the spec to be proven
      specMainModule :: !ModuleName
    , -- | Search order of the execution graph
      graphSearch :: GraphSearchOrder
    , -- | Whether to use bounded model checker
      bmc :: !Bool
    , -- | The file in which to save the proven claims in case the prover
      -- fails.
      saveProofs :: !(Maybe FilePath)
    }

parseModuleName :: String -> String -> String -> Parser ModuleName
parseModuleName metaName longName helpMsg =
    option
        readModuleName
        ( metavar metaName
            <> long longName
            <> help helpMsg
        )

readModuleName :: Options.ReadM ModuleName
readModuleName = do
    opt <- str
    case parseOnly (Lexer.parseModuleName <* Parser.eof) "<command-line>" opt of
        Left err -> readerError err
        Right something -> pure something

parseKoreProveOptions :: Parser KoreProveOptions
parseKoreProveOptions =
    KoreProveOptions
        <$> strOption
            ( metavar "SPEC_FILE"
                <> long "prove"
                <> help
                    "Kore source file representing spec to be proven.\
                    \Needs --spec-module."
            )
        <*> parseModuleName
            "SPEC_MODULE"
            "spec-module"
            "The name of the main module in the spec to be proven."
        <*> parseGraphSearch
        <*> switch
            ( long "bmc"
                <> help "Whether to use the bounded model checker."
            )
        <*> optional
            ( strOption
                ( long "save-proofs"
                    <> help
                        "The file in which to save the proven claims \
                        \in case the prover fails."
                )
            )
  where
    parseGraphSearch =
        option
            readGraphSearch
            ( metavar "GRAPH_SEARCH"
                <> long "graph-search"
                <> value BreadthFirst
                <> help
                    "Search order of the execution graph. \
                    \Either breadth-first or depth-first. \
                    \Default is breadth-first."
            )
      where
        searchOrders =
            [ ("breadth-first", BreadthFirst)
            , ("depth-first", DepthFirst)
            ]
        readGraphSearch = do
            input <- str
            let found = lookup input searchOrders
            case found of
                Just searchOrder -> pure searchOrder
                Nothing ->
                    let unknown = "Unknown search order '" ++ input ++ "'. "
                        names = intercalate ", " (fst <$> searchOrders)
                        known = "Known search order are: " ++ names
                     in readerError (unknown ++ known)

data KoreMergeOptions = KoreMergeOptions
    { -- | Name for file containing a sequence of rules to merge.
      rulesFileName :: !FilePath
    , maybeBatchSize :: Maybe Int
    }

parseKoreMergeOptions :: Parser KoreMergeOptions
parseKoreMergeOptions =
    KoreMergeOptions
        <$> strOption
            ( metavar "MERGE_RULES_FILE"
                <> long "merge-rules"
                <> help
                    "List of rules to merge."
            )
        <*> optional
            ( option
                (maybeReader readMaybe)
                ( metavar "MERGE_BATCH_SIZE"
                    <> long "merge-batch-size"
                    <> help
                        "The size of a merge batch."
                )
            )

{- | Record Type containing common command-line arguments for each executable in
the project
-}
data GlobalOptions = GlobalOptions
    { -- | Version flag [default=false]
      willVersion :: !Bool
    }

-- | Record type to store all state and options for the subMain operations
data MainOptions a = MainOptions
    { globalOptions :: !GlobalOptions
    , localOptions :: !(Maybe a)
    }

{- |
Global main function parses command line arguments, handles global flags
and returns the parsed options
-}
mainGlobal ::
    ExeName ->
    -- | environment variable name for extra arguments
    Maybe String ->
    -- | local options parser
    Parser options ->
    -- | option parser information
    InfoMod (MainOptions options) ->
    IO (MainOptions options)
mainGlobal exeName maybeEnv localOptionsParser modifiers = do
    options <- commandLineParse exeName maybeEnv localOptionsParser modifiers
    when (willVersion $ globalOptions options) mainVersion
    return options

-- | main function to print version information
mainVersion :: IO ()
mainVersion =
    mapM_
        putStrLn
        [ "Kore version " ++ packageVersion
        , "Git:"
        , "  revision:\t" ++ gitHash ++ if gitDirty then " (dirty)" else ""
        , "  branch:\t" ++ fromMaybe "<unknown>" gitBranch
        , "  last commit:\t" ++ gitCommitDate
        ]
  where
    packageVersion = showVersion MetaData.version
    VersionInfo{gitHash, gitDirty, gitBranch, gitCommitDate} = $versionInfo

--------------------
-- Option Parsers --

-- | Global Main argument parser for common options
globalCommandLineParser :: Parser GlobalOptions
globalCommandLineParser =
    GlobalOptions
        <$> flag
            False
            True
            ( long "version"
                <> help "Print version information"
            )

getArgs ::
    -- | environment variable name for extra arguments
    Maybe String ->
    IO ([String], [String])
getArgs maybeEnv = do
    args0 <- Env.getArgs
    args1 <-
        case maybeEnv of
            Nothing -> pure []
            Just env -> words . fromMaybe "" <$> Env.lookupEnv env
    pure (args0, args1)

-- | Run argument parser for local executable
commandLineParse ::
    ExeName ->
    -- | environment variable name for extra arguments
    Maybe String ->
    -- | local options parser
    Parser a ->
    -- | local parser info modifiers
    InfoMod (MainOptions a) ->
    IO (MainOptions a)
commandLineParse (ExeName exeName) maybeEnv parser infoMod = do
    (args, argsEnv) <- getArgs maybeEnv
    let allArgs = args <> argsEnv
        parseResult =
            execParserPure
                defaultPrefs
                (info parseMainOptions infoMod)
                allArgs
        changeHelpOverFailure
            | Just env <- maybeEnv = overFailure (changeHelp args env argsEnv)
            | otherwise = id
    handleParseResult $ changeHelpOverFailure parseResult
  where
    parseMainOptions =
        MainOptions
            <$> globalCommandLineParser
            <*> optional parser
            <**> helper

    changeHelp :: [String] -> String -> [String] -> ParserHelp -> ParserHelp
    changeHelp args env argsEnv parserHelp@ParserHelp{helpError} =
        parserHelp
            { helpError =
                vsepChunks [Chunk . Just $ commandWithOpts, helpError]
            }
      where
        commandWithOpts =
            Pretty.vsep
                [ Pretty.linebreak
                , Pretty.pretty (unwords (exeName : args))
                , Pretty.pretty env <> "=" <> Pretty.squotes (Pretty.pretty $ unwords argsEnv)
                ]

----------------------
-- Helper Functions --

-- | Time a pure computation and print results.
clockSomething :: String -> a -> Main a
clockSomething description something =
    clockSomethingIO description (liftIO $ evaluate something)

-- | Time an IO computation and print results.
clockSomethingIO :: String -> Main a -> Main a
clockSomethingIO description something = do
    start <- lift $ getTime Monotonic
    x <- something
    end <- lift $ getTime Monotonic
    logEntry $ logMessage end start
    return x
  where
    logMessage end start =
        mkMessage start end
    mkMessage start end =
        Log.LogMessage
            { message =
                pack $ description ++ " " ++ show (diffTimeSpec end start)
            , severity = Log.Info
            , callstack = emptyCallStack
            }

-- | Verify that a Kore pattern is well-formed and print timing information.
mainPatternVerify ::
    -- | Module containing definitions visible in the pattern
    VerifiedModule Attribute.Symbol ->
    -- | Parsed pattern to check well-formedness
    ParsedPattern ->
    Main Verified.Pattern
mainPatternVerify verifiedModule patt = do
    verifyResult <-
        clockSomething
            "Verifying the pattern"
            (runPatternVerifier context $ verifyStandalonePattern Nothing patt)
    either errorVerify return verifyResult
  where
    context =
        PatternVerifier.verifiedModuleContext verifiedModule
            & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers

lookupMainModule ::
    Monad monad =>
    ModuleName ->
    Map.Map ModuleName (VerifiedModule Attribute.Symbol) ->
    monad (VerifiedModule Attribute.Symbol)
lookupMainModule name modules =
    case Map.lookup name modules of
        Nothing ->
            error
                ( "The main module, '"
                    ++ getModuleNameForError name
                    ++ "', was not found. Check the --module flag."
                )
        Just m -> return m

{- | Verify the well-formedness of a Kore definition.

Also prints timing information; see 'mainParse'.
-}
verifyDefinitionWithBase ::
    -- | already verified definition
    ( Map.Map ModuleName (VerifiedModule Attribute.Symbol)
    , Map.Map Text AstLocation
    ) ->
    -- | Parsed definition to check well-formedness
    ParsedDefinition ->
    Main
        ( Map.Map ModuleName (VerifiedModule Attribute.Symbol)
        , Map.Map Text AstLocation
        )
verifyDefinitionWithBase
    alreadyVerified
    definition =
        do
            verifyResult <-
                clockSomething
                    "Verifying the definition"
                    ( verifyAndIndexDefinitionWithBase
                        alreadyVerified
                        Builtin.koreVerifiers
                        definition
                    )
            either errorVerify return verifyResult

{- | Parse a Kore definition from a filename.

Also prints timing information; see 'mainParse'.
-}
parseDefinition :: FilePath -> Main ParsedDefinition
parseDefinition = mainParse parseKoreDefinition

mainParse ::
    (FilePath -> Text -> Either String a) ->
    String ->
    Main a
mainParse parser fileName = do
    contents <-
        Text.readFile fileName
            & liftIO
            & clockSomethingIO "Reading the input file"
    parseResult <-
        clockSomething "Parsing the file" (parser fileName contents)
    case parseResult of
        Left err -> errorParse err
        Right definition -> return definition

type LoadedModule = VerifiedModule Attribute.Symbol

data LoadedDefinition = LoadedDefinition
    { indexedModules :: Map ModuleName LoadedModule
    , definedNames :: Map Text AstLocation
    , kFileLocations :: KFileLocations
    }

loadDefinitions :: [FilePath] -> Main LoadedDefinition
loadDefinitions filePaths =
    do
        loadedDefinitions & fmap sortClaims
  where
    loadedDefinitions = do
        parsedDefinitions <- traverse parseDefinition filePaths
        let attributes = fmap definitionAttributes parsedDefinitions
        sources <- traverse parseKFileAttributes attributes
        let sources' = filter notDefault (nub sources)
        (indexedModules, definedNames) <-
            Monad.foldM verifyDefinitionWithBase mempty parsedDefinitions
        return $
            LoadedDefinition
                indexedModules
                definedNames
                (KFileLocations sources')

    sortClaims :: LoadedDefinition -> LoadedDefinition
    sortClaims def@LoadedDefinition{indexedModules} =
        let indexedModules' = indexedModules & Lens.traversed %~ sortModuleClaims
         in def{indexedModules = indexedModules'}

loadModule :: ModuleName -> LoadedDefinition -> Main LoadedModule
loadModule moduleName = lookupMainModule moduleName . indexedModules

mainParseSearchPattern ::
    VerifiedModule StepperAttributes ->
    String ->
    Main (Pattern VariableName)
mainParseSearchPattern indexedModule patternFileName = do
    purePattern <- mainPatternParseAndVerify indexedModule patternFileName
    case purePattern of
        And_ _ term predicateTerm ->
            return
                Conditional
                    { term
                    , predicate =
                        either
                            (error . show . KorePretty.pretty)
                            id
                            (makePredicate predicateTerm)
                    , substitution = mempty
                    }
        _ -> error "Unexpected non-conjunctive pattern"

{- | IO action that parses a kore pattern from a filename, verifies it,
 converts it to a pure pattern, and prints timing information.
-}
mainPatternParseAndVerify ::
    VerifiedModule StepperAttributes ->
    String ->
    Main (TermLike VariableName)
mainPatternParseAndVerify indexedModule patternFileName =
    mainPatternParse patternFileName >>= mainPatternVerify indexedModule

{- | IO action that parses a kore pattern from a filename and prints timing
 information.
-}
mainPatternParse :: String -> Main ParsedPattern
mainPatternParse = mainParse parseKorePattern
