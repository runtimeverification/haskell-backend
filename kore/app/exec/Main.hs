module Main (main) where

import Control.Applicative
       ( Alternative (..), optional, (<$) )
import Data.List
       ( intercalate )
import Data.Maybe
       ( fromMaybe )
import Data.Reflection
import Data.Semigroup
       ( (<>) )
import Data.Text.Prettyprint.Doc.Render.Text
       ( hPutDoc, putDoc )
import Options.Applicative
       ( InfoMod, Parser, argument, auto, fullDesc, header, help, long,
       metavar, option, progDesc, readerError, str, strOption, value )
import System.Exit
       ( ExitCode (..), exitWith )
import System.IO
       ( IOMode (WriteMode), withFile )

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Kore.AST.Kore
                 ( CommonKorePattern, VerifiedKorePattern )
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.AST.Valid
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Error
                 ( printError )
import           Kore.Exec
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
import           Kore.Logger.Output
                 ( KoreLogOptions (..), parseKoreLogOptions, withLogger )
import           Kore.Parser.Parser
                 ( parseKorePattern )
import           Kore.Predicate.Predicate
                 ( makePredicate )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import           Kore.Step.Search
                 ( SearchType (..) )
import qualified Kore.Step.Search as Search
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.SmtLemma
import           Kore.Step.Step
import           Kore.Step.StepperAttributes
import           Kore.Unparser
                 ( unparse )
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
        <> help "Kore source file representing pattern to search for.\
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
        => String -> String -> String -> [(String,value)] -> Parser value
    parseSum metaName longName helpMsg options =
        option readSum
            (  metavar metaName
            <> long longName
            <> help helpMsg
            )
      where
        readSum = do
            opt <- str
            case lookup opt options of
                Just val -> pure val
                _ ->
                    let
                        unknown = "Unknown " ++  longName ++ " '" ++ opt ++ "'. "
                        known = "Known " ++ longName ++ "s are: " ++
                            intercalate ", " (map fst options) ++ "."
                    in
                        readerError (unknown ++ known)

applyKoreSearchOptions
    :: Maybe KoreSearchOptions
    -> KoreExecOptions
    -> KoreExecOptions
applyKoreSearchOptions koreSearchOptions koreExecOpts =
    case koreSearchOptions of
        Nothing -> koreExecOpts
        Just koreSearchOpts ->
            koreExecOpts
                { koreSearchOptions = Just koreSearchOpts
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
    , stepLimit           :: !(Limit Natural)
    , strategy            :: !([Rewrite] -> Strategy (Prim Rewrite))
    , koreLogOptions      :: !KoreLogOptions
    , koreSearchOptions   :: !(Maybe KoreSearchOptions)
    , koreProveOptions    :: !(Maybe KoreProveOptions)
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
                <> help "Verify and execute the Kore pattern found in PATTERN_FILE."
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
        <*> parseStepLimit
        <*> parseStrategy
        <*> parseKoreLogOptions
        <*> pure Nothing
        <*> optional parseKoreProveOptions
    SMT.Config { timeOut = defaultTimeOut } = SMT.defaultConfig
    readSMTTimeOut = do
        i <- auto
        if i <= 0
            then readerError "smt-timeout must be a positive integer."
            else return $ SMT.TimeOut $ Limit i
    parseStepLimit = Limit <$> depth <|> pure Unlimited
    parseStrategy =
        option readStrategy
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
        readStrategy = do
            strat <- str
            let found = lookup strat strategies
            case found of
                Just strategy -> pure strategy
                Nothing ->
                    let
                        unknown = "Unknown strategy '" ++ strat ++ "'. "
                        names = intercalate ", " (fst <$> strategies)
                        known = "Known strategies are: " ++ names
                    in
                        readerError (unknown ++ known)
    depth =
        option auto
            (  metavar "DEPTH"
            <> long "depth"
            <> help "Execute up to DEPTH steps."
            )
    parseMainModuleName =
        fmap ModuleName $ strOption info
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
    case localOptions options of
        Nothing ->
            -- global options parsed, but local failed; exit gracefully
            return ()
        Just koreExecOpts -> mainWithOptions koreExecOpts

mainWithOptions :: KoreExecOptions -> IO ()
mainWithOptions
    KoreExecOptions
        { definitionFileName
        , patternFileName
        , outputFileName
        , mainModuleName
        , smtTimeOut
        , smtPrelude
        , stepLimit
        , strategy
        , koreLogOptions
        , koreSearchOptions
        , koreProveOptions
        }
  = do
        let
            strategy' = Limit.replicate stepLimit . strategy
            smtConfig =
                SMT.defaultConfig
                    { SMT.timeOut = smtTimeOut
                    , SMT.preludeFile = smtPrelude
                    }
        parsedDefinition <- parseDefinition definitionFileName
        indexedDefinition@(indexedModules, _) <-
            verifyDefinitionWithBase
                Nothing
                True
                parsedDefinition
        indexedModule <-
            constructorFunctions <$> mainModule mainModuleName indexedModules
        searchParameters <-
            case koreSearchOptions of
                Nothing -> return Nothing
                Just KoreSearchOptions { searchFileName, bound, searchType } ->
                    do
                        searchPattern <-
                            mainParseSearchPattern indexedModule searchFileName
                        let searchConfig = Search.Config { bound, searchType }
                        (return . Just) (searchPattern, searchConfig)
        proveParameters <-
            case koreProveOptions of
                Nothing -> return Nothing
                Just KoreProveOptions { specFileName, specMainModule } ->
                    do
                        specDef <- parseDefinition specFileName
                        (specDefIndexedModules, _) <-
                            verifyDefinitionWithBase
                                (Just indexedDefinition)
                                True
                                specDef
                        specDefIndexedModule <-
                            mainModule specMainModule specDefIndexedModules
                        return (Just specDefIndexedModule)
        maybePurePattern <- case patternFileName of
            Nothing -> return Nothing
            Just fileName ->
                Just
                <$> mainPatternParseAndVerify
                    indexedModule
                    fileName
        (exitCode, finalPattern) <-
            clockSomethingIO "Executing"
            $ withLogger koreLogOptions (\logger ->
                SMT.runSMT smtConfig
                $ evalSimplifier logger
                $ do
                  give
                      (extractMetadataTools indexedModule
                          :: MetadataTools Object StepperAttributes
                      )
                      (declareSMTLemmas indexedModule)
                  case proveParameters of
                    Nothing -> do
                        let purePattern =
                                fromMaybe
                                    (error "Missing: --pattern PATTERN_FILE")
                                    maybePurePattern
                        case searchParameters of
                            Nothing -> do
                                pat <- exec indexedModule strategy' purePattern
                                exitCode <- execGetExitCode indexedModule strategy' pat
                                return (exitCode, pat)
                            Just (searchPattern, searchConfig) -> do
                                pat <-
                                    search
                                        indexedModule
                                        strategy'
                                        purePattern
                                        searchPattern
                                        searchConfig
                                return (ExitSuccess, pat)
                    Just specIndexedModule ->
                        either
                            (\pat -> (ExitFailure 1, pat))
                            (\_ -> (ExitSuccess, mkTop $ mkSortVariable "R" ))
                        <$> prove
                                stepLimit
                                indexedModule
                                specIndexedModule
                )
        let unparsed = (unparse . externalizeFreshVariables) finalPattern
        case outputFileName of
            Nothing ->
                putDoc unparsed
            Just outputFile ->
                withFile outputFile WriteMode (\h -> hPutDoc h unparsed)
        () <$ exitWith exitCode

-- | IO action that parses a kore pattern from a filename and prints timing
-- information.
mainPatternParse :: String -> IO CommonKorePattern
mainPatternParse = mainParse parseKorePattern

-- | IO action that parses a kore pattern from a filename, verifies it,
-- converts it to a pure patterm, and prints timing information.
mainPatternParseAndVerify
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> String
    -> IO (CommonStepPattern Object)
mainPatternParseAndVerify indexedModule patternFileName = do
    parsedPattern <- mainPatternParse patternFileName
    makePurePattern <$> mainPatternVerify indexedModule parsedPattern

mainParseSearchPattern
    :: VerifiedModule StepperAttributes Attribute.Axiom
    -> String
    -> IO (CommonExpandedPattern Object)
mainParseSearchPattern indexedModule patternFileName = do
    purePattern <- mainPatternParseAndVerify indexedModule patternFileName
    case purePattern of
        And_ _ term predicateTerm -> return
            Predicated
                { term
                , predicate =
                    either (error . printError) id
                        (makePredicate predicateTerm)
                , substitution = mempty
                }
        _ -> error "Unexpected non-conjunctive pattern"

makePurePattern
    :: VerifiedKorePattern
    -> CommonStepPattern Object
makePurePattern pat =
    case fromKorePattern Object pat of
        Left err -> error (printError err)
        Right objPat -> objPat
