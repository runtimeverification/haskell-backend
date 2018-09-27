module Main (main) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Arrow as Arrow
import           Control.Monad
                 ( when )
import           Data.Functor.Foldable
                 ( Fix (..), cata )
import           Data.List
                 ( intercalate )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( Given, give )
import           Data.Semigroup
                 ( (<>) )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           Options.Applicative
                 ( InfoMod, Parser, argument, auto, fullDesc, header, help,
                 long, metavar, option, progDesc, readerError, str, strOption,
                 value )

import           Kore.AST.Common
import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.AST.MetaOrObject
                 ( Meta, Object (..), asUnified )
import           Kore.AST.PureML
                 ( UnfixedCommonPurePattern, groundHead )
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartConstructors
                 ( mkApp, mkDomainValue )
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
                 ( MetadataTools (..), SymbolOrAliasSorts,
                 extractMetadataTools )
import           Kore.Parser.Parser
                 ( fromKore, fromKorePattern )
import           Kore.Predicate.Predicate
                 ( pattern PredicateTrue, makeMultipleOrPredicate,
                 makePredicate, makeTruePredicate, unwrapPredicate )
import           Kore.SMT.Config
import           Kore.Step.AxiomPatterns
                 ( AxiomPattern (..), koreIndexedModuleToAxiomPatterns )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Registry
                 ( axiomPatternsToEvaluators, extractAxiomPatterns )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Search
                 ( SearchConfiguration (..), SearchType (..), search )
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
                 ( unparseToString )
import           Kore.Variables.Free
                 ( pureAllVariables )
import           Kore.Variables.Fresh
                 ( FreshVariable, freshVariablePrefix )

import GlobalMain
       ( MainOptions (..), clockSomething, clockSomethingIO, enableDisableFlag,
       mainGlobal )

{-
Main module to run kore-exec
TODO: add command line argument tab-completion
-}

-- | Main options record
data KoreExecOptions = KoreExecOptions
    { definitionFileName  :: !FilePath
    -- ^ Name for a file containing a definition to verify and use for execution
    , patternFileName     :: !FilePath
    -- ^ Name for file containing a pattern to verify and use for execution
    , searchFileName      :: !FilePath
    -- ^ Name for file containing a pattern to search for during execution
    , outputFileName      :: !FilePath
    -- ^ Name for file to contain the output pattern
    , mainModuleName      :: !Text
    -- ^ The name of the main module in the definition
    , isKProgram          :: !Bool
    -- ^ Whether the pattern file represents a program to be put in the
    -- initial configuration before execution
    , smtTimeOut          :: !SMTTimeOut
    , stepLimit           :: !(Limit Natural)
    , boundLimit          :: !(Limit Natural)
    , strategy
        :: !([AxiomPattern Object] -> Strategy (Prim (AxiomPattern Object)))
    , searchType          :: !(Maybe SearchType)
    }

-- | Command Line Argument Parser
commandLineParser :: Parser KoreExecOptions
commandLineParser =
    KoreExecOptions
    <$> argument str
        (  metavar "DEFINITION_FILE"
        <> help "Kore definition file to verify and use for execution" )
    <*> strOption
        (  metavar "PATTERN_FILE"
        <> long "pattern"
        <> help "Kore pattern source file to verify and execute. Needs --module."
        <> value "" )
    <*> strOption
        (  metavar "SEARCH_FILE"
        <> long "search"
        <> help "Kore source file representing pattern to search for.\
                \Needs --module."
        <> value "" )
    <*> strOption
        (  metavar "PATTERN_OUTPUT_FILE"
        <> long "output"
        <> help "Output file to contain final Kore pattern."
        <> value "" )
    <*> strOption
        (  metavar "MODULE"
        <> long "module"
        <> help "The name of the main module in the Kore definition."
        <> value "" )
    <*> enableDisableFlag "is-program"
        True False False
        "Whether the pattern represents a program."
    <*> option
        ( do i <- auto
             if i <= 0
             then readerError "smt-timeout must be a positive integer."
             else return $ SMTTimeOut i
        )
        ( metavar "SMT_TIMEOUT"
        <> long "smt-timeout"
        <> help "Timeout for calls to the SMT solver, in milliseconds"
        <> value defaultSMTTimeOut
        )
    <*> parseStepLimit
    <*> parseBoundLimit
    <*> parseStrategy
    <*> parseSearchType
  where
    parseStepLimit = Limit <$> depth <|> pure Unlimited
    parseBoundLimit = Limit <$> bound <|> pure Unlimited
    parseStrategy =
        option readStrategy
            (  metavar "STRATEGY"
            <> long "strategy"
            -- TODO (thomas.tuegel): Make defaultStrategy the default when it
            -- works correctly.
            <> value simpleStrategy
            <> help "Select rewrites using STRATEGY."
            )
      where
        readStrategy = do
            strat <- str
            case strat of
                "simple" -> pure simpleStrategy
                "default" -> pure defaultStrategy
                _ ->
                    let
                        unknown = "Unknown strategy '" ++ strat ++ "'. "
                        known = "Known strategies are: simple, default."
                    in
                        readerError (unknown ++ known)
    depth =
        option auto
            (  metavar "DEPTH"
            <> long "depth"
            <> help "Execute up to DEPTH steps."
            )
    bound =
        option auto
            (  metavar "BOUND"
            <> long "bound"
            <> help "Maximum number of solutions."
            )
    parseSearchType =
        parseSumOption
            "SEARCH_TYPE"
            "searchType"
            Nothing
            "Search type (selects potential solutions)"
            (map (\ s -> (show s, Just s)) [ ONE, FINAL, STAR, PLUS ])


parseSumOption
    :: Eq value
    => String -> String -> value -> String -> [(String,value)] -> Parser value
parseSumOption metaName longName defaultValue helpMsg options =
    option readSumOption
        (  metavar metaName
        <> long longName
        <> value defaultValue
        <> help helpMsg
        )
  where
    readSumOption = do
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
                    freshPrefix <> (Text.drop (Text.length freshVariablePrefix) name)
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
  options <- mainGlobal commandLineParser parserInfoModifiers
  case localOptions options of
    Nothing -> return () -- global options parsed, but local failed; exit gracefully
    Just KoreExecOptions
        { definitionFileName
        , patternFileName
        , outputFileName
        , mainModuleName
        , smtTimeOut
        , isKProgram
        , stepLimit
        , strategy
        , searchFileName
        , boundLimit
        , searchType
        }
      -> do
        parsedDefinition <- mainDefinitionParse definitionFileName
        indexedModules <- mainVerify True parsedDefinition
        when (patternFileName /= "") $ do
            indexedModule <-
                constructorFunctions <$> mainModule (ModuleName mainModuleName) indexedModules
            purePattern <-
                mainPatternParseAndVerify indexedModule patternFileName
            let
                metadataTools = extractMetadataTools indexedModule
            finalPattern <- case searchType of
                Nothing -> clockSomething "Executing"
                    $ evalSimplifierWithTimeout smtTimeOut
                    $ do
                        axiomsAndSimplifiers <-
                            makeAxiomsAndSimplifiers indexedModule metadataTools
                        let
                            (rewriteAxioms, simplifier, substitutionSimplifier) =
                                axiomsAndSimplifiers
                            computeStrategy limit pat = runStrategy
                                (transitionRule metadataTools substitutionSimplifier simplifier)
                                (strategy rewriteAxioms)
                                limit
                                (pat, mempty)
                            runningPattern =
                                if isKProgram
                                    then give (symbolOrAliasSorts metadataTools)
                                        $ makeKInitConfig purePattern
                                    else purePattern
                            expandedPattern = makeExpandedPattern runningPattern
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
                        give (symbolOrAliasSorts metadataTools)
                            ExpandedPattern.toMLPattern . fst . pickLongest
                            <$> computeStrategy stepLimit initialPattern
                Just sType -> do
                    searchPattern <-
                        mainParseSearchPattern indexedModule metadataTools
                            searchFileName
                    clockSomething "Searching"
                        $ evalSimplifierWithTimeout smtTimeOut
                        $ do
                            axiomsAndSimplifiers <-
                                makeAxiomsAndSimplifiers indexedModule metadataTools
                            let
                                (rewriteAxioms, simplifier, substitutionSimplifier) =
                                    axiomsAndSimplifiers
                                computeStrategy limit pat = runStrategy
                                    (transitionRule metadataTools substitutionSimplifier simplifier)
                                    (strategy rewriteAxioms)
                                    limit
                                    (pat, mempty)
                                runningPattern =
                                    if isKProgram
                                        then give (symbolOrAliasSorts metadataTools)
                                            $ makeKInitConfig purePattern
                                        else purePattern
                                expandedPattern = makeExpandedPattern runningPattern
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
                            solutions <-
                                search
                                    metadataTools
                                    substitutionSimplifier
                                    simplifier
                                    computeStrategy
                                    SearchConfiguration
                                        { start = initialPattern
                                        , depth = stepLimit
                                        , bound = boundLimit
                                        , goal = searchPattern
                                        , searchType = sType
                                        }
                            let
                                (orPredicate, _proof) =
                                    give (symbolOrAliasSorts metadataTools)
                                    $ makeMultipleOrPredicate
                                    $ map
                                        ExpandedPattern.substitutionToPredicate
                                        solutions
                            return (unwrapPredicate orPredicate)
            let
                finalExternalPattern =
                    either (error . printError) id
                    (Builtin.externalizePattern indexedModule finalPattern)
                outputString =
                    unparseToString (externalizeFreshVars finalExternalPattern)
            if outputFileName /= ""
                then
                    writeFile outputFileName outputString
                else
                    putStrLn $ outputString

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

-- | IO action that parses a kore definition from a filename and prints timing
-- information.
mainDefinitionParse :: String -> IO KoreDefinition
mainDefinitionParse = mainParse fromKore

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
                    either (error . printError) fst
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

-- | IO action verifies well-formedness of Kore definition and prints
-- timing information.
mainVerify
    :: Bool -- ^ whether to check (True) or ignore attributes during verification
    -> KoreDefinition -- ^ Parsed definition to check well-formedness
    -> IO (Map.Map ModuleName (KoreIndexedModule StepperAttributes))
mainVerify willChkAttr definition =
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

makeKInitConfig
    :: (Given (SymbolOrAliasSorts Object))
    => CommonPurePattern Object
    -> CommonPurePattern Object
makeKInitConfig pat =
    mkApp initTCellHead
        [ mkApp mapElementHead
            [ mkApp kSeqHead
                [ mkApp (injHead configVarSort kItemSort)
                    [ mkDomainValue configVarSort
                        $ BuiltinDomainPattern
                        $ StringLiteral_ "$PGM"
                    ]
                , mkApp dotKHead []
                ]
            , pat
            ]
        ]

initTCellHead :: SymbolOrAlias Object
initTCellHead = groundHead "LblinitTCell" AstLocationImplicit

kSeqHead :: SymbolOrAlias Object
kSeqHead = groundHead "kseq" AstLocationImplicit

dotKHead :: SymbolOrAlias Object
dotKHead = groundHead "dotk" AstLocationImplicit

mapElementHead :: SymbolOrAlias Object
mapElementHead = groundHead "Lbl'UndsPipe'-'-GT-Unds'" AstLocationImplicit

injHead :: Sort Object -> Sort Object -> SymbolOrAlias Object
injHead fromSort toSort =
    SymbolOrAlias
    { symbolOrAliasConstructor = Id
        { getId = "inj"
        , idLocation = AstLocationImplicit
        }
    , symbolOrAliasParams = [fromSort, toSort]
    }


groundObjectSort :: Text -> Sort Object
groundObjectSort name =
    SortActualSort
        SortActual
        { sortActualName =
            Id
            { getId = name
            , idLocation = AstLocationImplicit
            }
        , sortActualSorts = []
        }

configVarSort :: Sort Object
configVarSort = groundObjectSort "SortKConfigVar"

kItemSort :: Sort Object
kItemSort = groundObjectSort "SortKItem"

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
    :: (CommonPurePattern Object
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
        (  [AxiomPattern Object]
        , PureMLPatternSimplifier Object Variable
        , PredicateSubstitutionSimplifier Object
        )
makeAxiomsAndSimplifiers indexedModule tools =
    do
        functionAxioms <-
            simplifyFunctionAxioms
                (extractAxiomPatterns Object indexedModule)
        rewriteAxioms <-
            simplifyRewriteAxioms
                (koreIndexedModuleToAxiomPatterns Object indexedModule)
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
                :: PredicateSubstitutionSimplifier Object
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
