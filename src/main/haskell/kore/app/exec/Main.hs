module Main (main) where

import           Control.Applicative
                 ( Alternative (..), optional )
import qualified Control.Arrow as Arrow
import           Data.Functor.Foldable
                 ( Fix (..), cata )
import           Data.List
                 ( intercalate )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )
import           Data.Semigroup
                 ( (<>) )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           Data.Text.Prettyprint.Doc.Render.Text
                 ( hPutDoc, putDoc )
import           Options.Applicative
                 ( InfoMod, Parser, argument, auto, fullDesc, header, help,
                 long, metavar, option, progDesc, readerError, str, strOption,
                 value )
import           System.IO
                 ( IOMode (WriteMode), withFile )

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Kore.AST.Common
import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.AST.MetaOrObject
                 ( Meta, Object (..), asUnified )
import           Kore.AST.PureML
                 ( UnfixedCommonPurePattern )
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (DoNotVerifyAttributes),
                 defaultAttributesVerification, verifyAndIndexDefinition )
import           Kore.ASTVerifier.PatternVerifier
                 ( verifyStandalonePattern )
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( printError )
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), KoreIndexedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), extractMetadataTools )

import           Kore.Parser.Parser
                 ( fromKore, fromKorePattern )
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeMultipleOrPredicate,
                 makePredicate, makeTruePredicate, unwrapPredicate )
import           Kore.SMT.Config
import           Kore.Step.AxiomPatterns
                 ( AxiomPattern (..), extractRewriteAxioms )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Registry
                 ( axiomPatternsToEvaluators, extractFunctionAxioms )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( toPredicate )
import           Kore.Step.Search
                 ( SearchType (..), search )
import qualified Kore.Step.Search as Search
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier (..),
                 PureMLPatternSimplifier, SimplificationProof (..), Simplifier,
                 defaultSMTTimeOut, evalSimplifierWithTimeout )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Simplification.PredicateSubstitution as PredicateSubstitution
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.Step
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Substitution.Class
                 ( Hashable, substitute )
import qualified Kore.Substitution.List as ListSubstitution
import           Kore.Unparser
                 ( unparse )
import           Kore.Variables.Free
                 ( pureAllVariables )
import           Kore.Variables.Fresh
                 ( FreshVariable, freshVariablePrefix )

import GlobalMain
       ( MainOptions (..), clockSomething, clockSomethingIO, mainGlobal )


{-
Main module to run kore-exec
TODO: add command line argument tab-completion
-}

data KoreSearchOptions =
    KoreSearchOptions
        { searchFileName :: !FilePath
        -- ^ Name of file containing a pattern to match during execution
        , boundLimit :: !(Limit Natural)
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
    <*> parseBoundLimit
    <*> parseSearchType
  where
    parseBoundLimit = Limit <$> bound <|> pure Unlimited
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
                    allAxioms
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
    , patternFileName     :: !FilePath
    -- ^ Name for file containing a pattern to verify and use for execution
    , outputFileName      :: !(Maybe FilePath)
    -- ^ Name for file to contain the output pattern
    , mainModuleName      :: !ModuleName
    -- ^ The name of the main module in the definition
    , smtTimeOut          :: !SMTTimeOut
    , stepLimit           :: !(Limit Natural)
    , strategy
        :: !([AxiomPattern Object] -> Strategy (Prim (AxiomPattern Object)))
    , koreSearchOptions   :: !(Maybe KoreSearchOptions)
    }

-- | Command Line Argument Parser
parseKoreExecOptions :: Parser KoreExecOptions
parseKoreExecOptions =
    applyKoreSearchOptions
        <$> optional parseKoreSearchOptions
        <*> parseKoreExecOptions0
  where
    parseKoreExecOptions0 =
        KoreExecOptions
        <$> argument str
            (  metavar "DEFINITION_FILE"
            <> help "Kore definition file to verify and use for execution" )
        <*> strOption
            (  metavar "PATTERN_FILE"
            <> long "pattern"
            <> help "Verify and execute the Kore pattern found in PATTERN_FILE."
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
            <> value defaultSMTTimeOut
            )
        <*> parseStepLimit
        <*> parseStrategy
        <*> pure Nothing
    readSMTTimeOut = do
        i <- auto
        if i <= 0
            then readerError "smt-timeout must be a positive integer."
            else return $ SMTTimeOut i
    parseStepLimit = Limit <$> depth <|> pure Unlimited
    parseStrategy =
        option readStrategy
            (  metavar "STRATEGY"
            <> long "strategy"
            -- TODO (thomas.tuegel): Make defaultStrategy the default when it
            -- works correctly.
            <> value anyAxiom
            <> help "Select rewrites using STRATEGY."
            )
      where
        strategies =
            [ ("any", anyAxiom)
            , ("all", allAxioms)
            , ("any-heating-cooling", heatingCooling anyAxiom)
            , ("all-heating-cooling", heatingCooling allAxioms)
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

externalizeFreshVars :: CommonPurePattern level -> CommonPurePattern level
externalizeFreshVars pat = cata renameFreshLocal pat
  where
    allVarsIds :: Set.Set Text
    allVarsIds = Set.map (getId . variableName) (pureAllVariables pat)
    freshVarsIds :: Set.Set Text
    freshVarsIds = Set.filter (Text.isPrefixOf freshVariablePrefix) allVarsIds
    computeFreshPrefix :: Text -> (Set.Set Text) -> Text
    computeFreshPrefix pref strings
      | Set.null matchingStrings = pref
      -- TODO(traiansf): if executing multiple times (like in stepping),
      -- names for generated fresh variables will grow longer and longer.
      -- Consider a mechanism to avoid this.
      | otherwise = computeFreshPrefix (pref <> "-") matchingStrings
      where
        matchingStrings :: Set.Set Text
        matchingStrings = Set.filter (Text.isPrefixOf pref) strings
    freshPrefix :: Text
    freshPrefix =
        computeFreshPrefix "var"
            (Set.filter (not . (Text.isPrefixOf freshVariablePrefix)) allVarsIds)
    renameFreshLocal :: UnfixedCommonPurePattern level -> CommonPurePattern level
    renameFreshLocal (VariablePattern v@(Variable {variableName}))
      | name `Set.member` freshVarsIds =
        Var_ v {
            variableName = variableName
                { getId =
                    freshPrefix <> Text.filter (/= '_') name
                }
        }
      where
        name :: Text
        name = getId variableName
    renameFreshLocal pat' = Fix pat'

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
        , stepLimit
        , strategy
        , koreSearchOptions
        }
  = do
        parsedDefinition <- parseDefinition definitionFileName
        indexedModules <- verifyDefinition True parsedDefinition
        indexedModule <-
            constructorFunctions <$> mainModule mainModuleName indexedModules
        purePattern <-
            mainPatternParseAndVerify indexedModule patternFileName
        let
            metadataTools = extractMetadataTools indexedModule
            MetadataTools { symbolOrAliasSorts } = metadataTools
        searchConfig <-
            case koreSearchOptions of
                Nothing -> return Nothing
                Just searchOptions@KoreSearchOptions { searchFileName } ->
                    do
                        searchPattern <-
                            mainParseSearchPattern
                                indexedModule
                                metadataTools
                                searchFileName
                        (return . Just) (searchPattern, searchOptions)
        finalPattern <-
            clockSomething "Executing"
            $ evalSimplifierWithTimeout smtTimeOut
            $ do
                axiomsAndSimplifiers <-
                    makeAxiomsAndSimplifiers indexedModule metadataTools
                let
                    (rewriteAxioms, simplifier, substitutionSimplifier) =
                        axiomsAndSimplifiers
                    runStrategy' pat =
                        runStrategy
                            (transitionRule
                                metadataTools
                                substitutionSimplifier
                                simplifier
                            )
                            (Limit.replicate stepLimit (strategy rewriteAxioms))
                            (pat, mempty)
                    expandedPattern = makeExpandedPattern purePattern
                simplifiedPatterns <-
                    ExpandedPattern.simplify
                        metadataTools
                        substitutionSimplifier
                        simplifier
                        expandedPattern
                let
                    initialPattern =
                        case
                            OrOfExpandedPattern.extractPatterns
                                (fst simplifiedPatterns) of
                            [] -> ExpandedPattern.bottom
                            (config : _) -> config
                executionTree <- runStrategy' initialPattern
                case searchConfig of
                    Nothing -> give symbolOrAliasSorts $ do
                        let (finalConfig, _) = pickLongest executionTree
                        return (ExpandedPattern.toMLPattern finalConfig)
                    Just (searchPattern, searchOptions) -> do
                        let
                            KoreSearchOptions { boundLimit, searchType } = searchOptions
                            match target (config, _proof) =
                                Search.matchWith
                                    metadataTools
                                    substitutionSimplifier
                                    simplifier
                                    target
                                    config
                        solutions <-
                            search
                                Search.Config
                                    { bound = boundLimit
                                    , searchType = searchType
                                    }
                                (match searchPattern)
                                executionTree
                        let
                            orPredicate =
                                give symbolOrAliasSorts
                                $ makeMultipleOrPredicate
                                $ fmap
                                    PredicateSubstitution.toPredicate
                                    solutions
                        return (unwrapPredicate orPredicate)
        let
            finalExternalPattern =
                either (error . printError) id
                (Builtin.externalizePattern indexedModule finalPattern)
            unparsed =
                (unparse . externalizeFreshVars) finalExternalPattern
        case outputFileName of
            Nothing ->
                putDoc unparsed
            Just outputFile ->
                withFile outputFile WriteMode (\h -> hPutDoc h unparsed)

mainModule
    :: ModuleName
    -> Map.Map ModuleName (KoreIndexedModule StepperAttributes)
    -> IO (KoreIndexedModule StepperAttributes)
mainModule name modules =
    case Map.lookup name modules of
        Nothing ->
            error
                (  "The main module, '"
                ++ getModuleNameForError name
                ++ "', was not found. Check the --module flag."
                )
        Just m -> return m

{- | Parse a Kore definition from a filename.

Also prints timing information; see 'mainParse'.

 -}
parseDefinition :: FilePath -> IO KoreDefinition
parseDefinition = mainParse fromKore

-- | IO action that parses a kore pattern from a filename and prints timing
-- information.
mainPatternParse :: String -> IO CommonKorePattern
mainPatternParse = mainParse fromKorePattern

-- | IO action that parses a kore pattern from a filename, verifies it,
-- converts it to a pure patterm, and prints timing information.
mainPatternParseAndVerify
    :: KoreIndexedModule StepperAttributes
    -> String
    -> IO (CommonPurePattern Object)
mainPatternParseAndVerify indexedModule patternFileName
  = do
    parsedPattern <- mainPatternParse patternFileName
    mainPatternVerify indexedModule parsedPattern
    return (makePurePattern parsedPattern)

mainParseSearchPattern
    :: KoreIndexedModule StepperAttributes
    -> MetadataTools Object StepperAttributes
    -> String
    -> IO (CommonExpandedPattern Object)
mainParseSearchPattern indexedModule tools patternFileName
  = do
    purePattern <- mainPatternParseAndVerify indexedModule patternFileName
    case purePattern of
        And_ _ term predicateTerm -> return
            Predicated
                { term
                , predicate =
                    either (error . printError) id
                        (give (symbolOrAliasSorts tools)
                            makePredicate predicateTerm
                        )
                , substitution = []
                }
        _ -> error "Unexpected non-conjunctive pattern"

-- | IO action that parses a kore AST entity from a filename and prints timing
-- information.
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

{- | Verify the well-formedness of a Kore definition.

Also prints timing information; see 'mainParse'.

 -}
verifyDefinition
    :: Bool -- ^ whether to check (True) or ignore attributes during verification
    -> KoreDefinition -- ^ Parsed definition to check well-formedness
    -> IO (Map.Map ModuleName (KoreIndexedModule StepperAttributes))
verifyDefinition willChkAttr definition =
    let attributesVerification =
            if willChkAttr
            then defaultAttributesVerification Proxy
            else DoNotVerifyAttributes
    in do
      verifyResult <-
        clockSomething "Verifying the definition"
            (verifyAndIndexDefinition
                attributesVerification
                Builtin.koreVerifiers
                definition
            )
      case verifyResult of
        Left err1            -> error (printError err1)
        Right indexedModules -> return indexedModules


-- | IO action verifies well-formedness of Kore patterns and prints
-- timing information.
mainPatternVerify
    :: KoreIndexedModule StepperAttributes
    -- ^ Module containing definitions visible in the pattern
    -> CommonKorePattern -- ^ Parsed pattern to check well-formedness
    -> IO ()
mainPatternVerify indexedModule patt =
    do
      verifyResult <-
        clockSomething "Verifying the pattern"
            (verifyStandalonePattern patternVerifier indexedModule patt)
      case verifyResult of
        Left err1 -> error (printError err1)
        Right _   -> return ()
  where
    Builtin.Verifiers { patternVerifier } = Builtin.koreVerifiers

makePurePattern
    :: CommonKorePattern
    -> CommonPurePattern Object
makePurePattern pat =
    case patternKoreToPure Object pat of
        Left err -> error (printError err)
        Right objPat -> objPat

makeExpandedPattern
    :: CommonPurePattern Object
    -> CommonExpandedPattern Object
makeExpandedPattern pat =
    Predicated
    { term = pat
    , predicate = makeTruePredicate
    , substitution = []
    }

-- TODO (traiansf): Get rid of this.
-- The function below works around several limitations of
-- the current tool by tricking the tool into believing that
-- functions are constructors (so that function patterns can match)
-- and that @kseq@ and @dotk@ are both functional and constructor.
constructorFunctions
    :: KoreIndexedModule StepperAttributes
    -> KoreIndexedModule StepperAttributes
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
    constructorFunctions1 h (atts, defn) =
        ( atts
            { isConstructor = isConstructor atts || isCons h
            , isFunctional = isFunctional atts || isCons h || isInj h
            , isInjective = isInjective atts || isCons h || isInj h
            , isSortInjection = isSortInjection atts || isInj h
            }
        , defn
        )

    isInj :: Id Object -> Bool
    isInj ident = getId ident == "inj"

    isCons :: Id Object -> Bool
    isCons ident = elem (getId ident) ["kseq", "dotk"]

    recurseIntoImports (attrs, attributes, importedModule) =
        (attrs, attributes, constructorFunctions importedModule)

preSimplify
    ::  (  CommonPurePattern Object
        -> Simplifier
            (OrOfExpandedPattern Object Variable, SimplificationProof Object)
        )
    -> AxiomPattern Object
    -> Simplifier (AxiomPattern Object)
preSimplify simplifier
    AxiomPattern
    { axiomPatternLeft = lhs
    , axiomPatternRight = rhs
    , axiomPatternRequires = requires
    , axiomPatternAttributes = atts
    }
  = do
    (simplifiedOrLhs, _proof) <- simplifier lhs
    let
        [Predicated {term, predicate = PredicateTrue, substitution}] =
            OrOfExpandedPattern.extractPatterns simplifiedOrLhs
        listSubst =
            ListSubstitution.fromList
                (map (Arrow.first asUnified) substitution)
    newLhs <- substitute term listSubst
    newRhs <- substitute rhs listSubst
    newRequires <- traverse (`substitute` listSubst) requires
    return AxiomPattern
        { axiomPatternLeft = newLhs
        , axiomPatternRight = newRhs
        , axiomPatternRequires = newRequires
        , axiomPatternAttributes = atts
        }

makeAxiomsAndSimplifiers
    :: KoreIndexedModule StepperAttributes
    -> MetadataTools Object StepperAttributes
    -> Simplifier
        ( [AxiomPattern Object]
        , PureMLPatternSimplifier Object Variable
        , PredicateSubstitutionSimplifier Object Simplifier
        )
makeAxiomsAndSimplifiers indexedModule tools =
    do
        functionAxioms <-
            simplifyFunctionAxioms
                (extractFunctionAxioms Object indexedModule)
        rewriteAxioms <-
            simplifyRewriteAxioms
                (extractRewriteAxioms Object indexedModule)
        let
            functionEvaluators =
                axiomPatternsToEvaluators functionAxioms
            functionRegistry =
                Map.unionWith (++)
                    -- user-defined functions
                    functionEvaluators
                    -- builtin functions
                    (Builtin.koreEvaluators indexedModule)
            simplifier
                ::  ( SortedVariable variable
                    , Ord (variable Meta)
                    , Ord (variable Object)
                    , Show (variable Meta)
                    , Show (variable Object)
                    , FreshVariable variable
                    , Hashable variable
                    )
                => PureMLPatternSimplifier Object variable
            simplifier = Simplifier.create tools functionRegistry
            substitutionSimplifier
                :: PredicateSubstitutionSimplifier Object Simplifier
            substitutionSimplifier =
                PredicateSubstitution.create tools simplifier
        return (rewriteAxioms, simplifier, substitutionSimplifier)
  where
    simplifyFunctionAxioms = mapM (mapM (preSimplify emptyPatternSimplifier))
    simplifyRewriteAxioms = mapM (preSimplify emptyPatternSimplifier)
    emptySimplifier
        ::  ( SortedVariable variable
            , Ord (variable Meta)
            , Ord (variable Object)
            , Show (variable Meta)
            , Show (variable Object)
            , FreshVariable variable
            , Hashable variable
            )
        => PureMLPatternSimplifier Object variable
    emptySimplifier = Simplifier.create tools Map.empty
    emptySubstitutionSimplifier =
        PredicateSubstitution.create tools emptySimplifier
    emptyPatternSimplifier =
        ExpandedPattern.simplify
            tools
            emptySubstitutionSimplifier
            emptySimplifier
        . makeExpandedPattern
