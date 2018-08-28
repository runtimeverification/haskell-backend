module Main (main) where

import           Control.Monad
                 ( when )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( Given, give )
import           Data.Semigroup
                 ( (<>) )
import           Options.Applicative
                 ( InfoMod, Parser, argument, fullDesc, header, help, long,
                 metavar, progDesc, str, strOption, value )

import           Kore.AST.Common
import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.AST.MetaOrObject
                 ( Object (..) )
import           Kore.AST.PureML
                 ( CommonPurePattern, groundHead )
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.AST.Sentence
                 ( KoreDefinition, ModuleName (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkApp, mkDomainValue, mkStringLiteral )
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (DoNotVerifyAttributes),
                 defaultAttributesVerification, verifyAndIndexDefinition )
import           Kore.ASTVerifier.PatternVerifier
                 ( verifyStandalonePattern )
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( printError )
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SortTools, extractMetadataTools )
import           Kore.Parser.Parser
                 ( fromKore, fromKorePattern )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( koreIndexedModuleToAxiomPatterns )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Registry
                 ( extractEvaluators )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import           Kore.Step.Step
                 ( MaxStepCount (AnyStepCount), pickFirstStepper )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Unparser.Unparse
                 ( unparseToString )

import GlobalMain
       ( MainOptions (..), clockSomething, clockSomethingIO, enableDisableFlag,
       mainGlobal )

{-
Main module to run kore-exec
TODO: add command line argument tab-completion
-}

-- | Main options record
data KoreExecOptions = KoreExecOptions
    { definitionFileName  :: !String
    -- ^ Name for a file containing a definition to verify and use for execution
    , patternFileName     :: !String
    -- ^ Name for file containing a pattern to verify and use for execution
    , mainModuleName      :: !String
    -- ^ The name of the main module in the definition
    , isKProgram          :: !Bool
    -- ^ Whether the pattern file represents a program to be put in the
    -- initial configuration before execution
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
        (  metavar "MODULE"
        <> long "module"
        <> help "The name of the main module in the Kore definition."
        <> value "" )
    <*> enableDisableFlag "is-program"
        True False False
        "Whether the pattern represents a program."


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
  options <- mainGlobal commandLineParser parserInfoModifiers
  case localOptions options of
    Nothing -> return () -- global options parsed, but local failed; exit gracefully
    Just KoreExecOptions
        { definitionFileName
        , patternFileName
        , mainModuleName
        , isKProgram
        }
      -> do
        parsedDefinition <- mainDefinitionParse definitionFileName
        indexedModules <- mainVerify True parsedDefinition
        when (patternFileName /= "") $ do
            parsedPattern <- mainPatternParse patternFileName
            indexedModule <-
                mainModule (ModuleName mainModuleName) indexedModules
            mainPatternVerify indexedModule parsedPattern
            let
                functionRegistry =
                    Map.unionWith (++)
                        -- user-defined functions
                        (extractEvaluators Object indexedModule)
                        -- builtin functions
                        (Builtin.koreEvaluators indexedModule)
                axiomPatterns =
                    koreIndexedModuleToAxiomPatterns Object indexedModule
                metadataTools = constructorFunctions (extractMetadataTools indexedModule)
                purePattern = makePurePattern parsedPattern
                runningPattern =
                    if isKProgram
                        then give (sortTools metadataTools)
                            $ makeKInitConfig purePattern
                        else purePattern
                expandedPattern = makeExpandedPattern runningPattern
            finalExpandedPattern <- clockSomething "Executing"
                    $ either (error . Kore.Error.printError) fst
                    $ evalSimplifier
                    $ do
                        simplifiedPatterns <-
                            ExpandedPattern.simplify
                                metadataTools
                                functionRegistry
                                expandedPattern
                        let
                            initialPattern =
                                case
                                    OrOfExpandedPattern.extractPatterns
                                        (fst simplifiedPatterns) of
                                    [] -> ExpandedPattern.bottom
                                    (config : _) -> config
                        pickFirstStepper
                            metadataTools
                            functionRegistry
                            axiomPatterns
                            AnyStepCount
                            initialPattern
            putStrLn $ unparseToString
                (ExpandedPattern.term finalExpandedPattern)

mainModule
    :: ModuleName
    -> Map.Map ModuleName (KoreIndexedModule StepperAttributes)
    -> IO (KoreIndexedModule StepperAttributes)
mainModule name modules =
    case Map.lookup name modules of
        Nothing ->
            error
                (  "The main module, '"
                ++ getModuleName name
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
    ExpandedPattern
    { term = pat
    , predicate = makeTruePredicate
    , substitution = []
    }

makeKInitConfig
    :: (Given (SortTools Object))
    => CommonPurePattern Object
    -> CommonPurePattern Object
makeKInitConfig pat =
    mkApp initTCellHead
        [ mkApp mapElementHead
            [ mkApp (injHead configVarSort kSort)
                [ mkDomainValue configVarSort
                  $ mkStringLiteral (StringLiteral "$PGM")
                ]
            , pat
            ]
        ]

initTCellHead :: SymbolOrAlias Object
initTCellHead = groundHead "LblinitTCell" AstLocationImplicit

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


groundObjectSort :: String -> Sort Object
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

kSort :: Sort Object
kSort = groundObjectSort "SortK"

-- TODO (traiansf): Get rid of this.
-- The function below works around several limitations of
-- the current tool by tricking the tool into believing that
-- functions are constructors (so that function patterns can match)
-- and that @inj@ is both functional and constructor.
constructorFunctions :: MetadataTools Object StepperAttributes -> MetadataTools Object StepperAttributes
constructorFunctions tools =
    tools
    { symAttributes = \h -> let atts = symAttributes tools h in
        atts
        { isConstructor = isConstructor atts || isFunction atts || isInj h
        , isFunctional = isFunctional atts || isInj h
        }
    }
  where
    isInj :: SymbolOrAlias Object -> Bool
    isInj h = getId (symbolOrAliasConstructor h) == "inj"
