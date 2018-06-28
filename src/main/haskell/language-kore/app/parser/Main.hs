{-# LANGUAGE NamedFieldPuns #-}

module Main
  ( main
  ) where

import           Control.Monad                            (when)
import           Data.Char                                (isSpace)
import qualified Data.Map                                 as Map
import           Data.Maybe                               (mapMaybe)
import           Data.Ord                                 (comparing)
import           Data.Semigroup                           ((<>))
import           Options.Applicative                      (InfoMod, Parser,
                                                           argument, fullDesc,
                                                           header, help, long,
                                                           metavar, progDesc,
                                                           str, strOption,
                                                           value)

import           Data.Kore.AST.Common                     (And (..),
                                                           Application (..),
                                                           AstLocation (..),
                                                           Equals (..), Id (..),
                                                           Implies (..),
                                                           Pattern (..),
                                                           Sort (..),
                                                           SortVariable (..),
                                                           SymbolOrAlias (..),
                                                           Variable (..))
import           Data.Kore.AST.Kore                       (CommonKorePattern,
                                                           UnifiedPattern (..),
                                                           UnifiedSortVariable)
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML                     (fromPurePattern)
import           Data.Kore.AST.PureToKore                 (patternKoreToPure)
import           Data.Kore.AST.Sentence                   (KoreDefinition,
                                                           ModuleName (..),
                                                           SentenceAxiom (..))
import           Data.Kore.ASTPrettyPrint                 (prettyPrintToString)
import           Data.Kore.ASTVerifier.DefinitionVerifier (AttributesVerification (DoNotVerifyAttributes),
                                                           defaultAttributesVerification,
                                                           verifyAndIndexDefinition)
import           Data.Kore.ASTVerifier.PatternVerifier    (verifyStandalonePattern)
import           Data.Kore.Error                          (printError)
import           Data.Kore.IndexedModule.IndexedModule    (IndexedModule (..),
                                                           KoreIndexedModule)
import           Data.Kore.IndexedModule.MetadataTools    (MetadataTools (..),
                                                           extractMetadataTools)
import           Data.Kore.Parser.Parser                  (fromKore,
                                                           fromKorePattern)
import           Data.Kore.Step.BaseStep                  (AxiomPattern (..))
import           Data.Kore.Step.Function.Data             (ApplicationFunctionEvaluator (..),
                                                           FunctionResult (..))
import           Data.Kore.Step.Function.Evaluator        (evaluateFunctions)
import           Data.Kore.Step.Function.UserDefined      (axiomFunctionEvaluator)
import           Data.Kore.Unparser.Unparse               (Unparse,
                                                           unparseToString)
import           Data.Kore.Variables.Fresh.IntCounter     (runIntCounter)
import           Data.List                                (groupBy, sortBy)

import           GlobalMain                               (MainOptions (..),
                                                           clockSomething,
                                                           clockSomethingIO,
                                                           enableDisableFlag,
                                                           mainGlobal)

{-
Main module to run kore-parser
TODO: add command line argument tab-completion
-}

-- | Main options record
data KoreParserOptions = KoreParserOptions
    { fileName        :: !String
    -- ^ Name for a file containing a definition to parse and verify
    , patternFileName :: !String
    -- ^ Name for file containing a pattern to parse and verify
    , mainModuleName  :: !String
    -- ^ the name of the main module in the definition
    , willPrint       :: !Bool   -- ^ Option to print definition
    , willVerify      :: !Bool   -- ^ Option to verify definition
    , willChkAttr     :: !Bool
    -- ^ Option to check attributes during verification
    , willEvaluate    :: !Bool   -- ^ Option to evaluate the pattern.
    }

-- | Command Line Argument Parser
commandLineParser :: Parser KoreParserOptions
commandLineParser =
    KoreParserOptions
    <$> argument str
        (  metavar "FILE"
        <> help "Kore source file to parse [and verify]" )
    <*> strOption
        (  metavar "PATTERN_FILE"
        <> long "pattern"
        <> help "Kore pattern source file to parse [and verify]. Needs --module."
        <> value "" )
    <*> strOption
        (  metavar "MODULE"
        <> long "module"
        <> help "The name of the main module in the Kore definition"
        <> value "" )
    <*> enableDisableFlag "print"
        True False True
        "printing parsed definition to stdout [default enabled]"
    <*> enableDisableFlag "verify"
        True False True
        "Verify well-formedness of parsed definition [default enabled]"
    <*> enableDisableFlag "chkattr"
        True False True
            "attributes checking during verification [default enabled]"
    <*> enableDisableFlag "evaluate"
        True False True
        "evaluate the --pattern"


-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
    <> progDesc "Parses Kore definition in FILE; optionally, \
                \Verifies well-formedness"
    <> header "kore-parser - a parser for Kore definitions"


-- | Parses a kore file and Check wellformedness
main :: IO ()
main = do
  options <- mainGlobal commandLineParser parserInfoModifiers
  case localOptions options of
    Nothing -> return () -- global options parsed, but local failed; exit gracefully
    Just KoreParserOptions
        { fileName
        , patternFileName
        , mainModuleName
        , willPrint
        , willVerify
        , willChkAttr
        , willEvaluate
        }
      -> do
        parsedDefinition <- mainDefinitionParse fileName
        indexedModules <- if willVerify
            then mainVerify willChkAttr parsedDefinition
            else return Map.empty
        -- when willPrint $ putStrLn (prettyPrintToString parsedDefinition)

        when (patternFileName /= "") $ do
            parsedPattern <- mainPatternParse patternFileName
            when willVerify $ do
                indexedModule <-
                    mainModule (ModuleName mainModuleName) indexedModules
                mainPatternVerify indexedModule parsedPattern
            when willPrint  $ putStrLn (prettyUnparseToString parsedPattern)
            when willEvaluate $ do
                indexedModule <-
                    mainModule (ModuleName mainModuleName) indexedModules
                functionResult <-
                    mainEvaluatePattern indexedModule parsedPattern
                when willPrint $
                    putStrLn (prettyUnparseToString (functionResultPattern functionResult))

mainModule
    :: ModuleName
    -> Map.Map ModuleName KoreIndexedModule
    -> IO KoreIndexedModule
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
    -> IO (Map.Map ModuleName KoreIndexedModule)
mainVerify willChkAttr definition =
    let attributesVerification =
            if willChkAttr
            then case defaultAttributesVerification of
                   Left err           -> error (printError err)
                   Right verification -> verification
            else DoNotVerifyAttributes
    in do
      verifyResult <-
        clockSomething "Verifying the definition"
            ( verifyAndIndexDefinition attributesVerification definition )
      case verifyResult of
        Left err1            -> error (printError err1)
        Right indexedModules -> return indexedModules

-- | IO action verifies well-formedness of Kore patterns and prints
-- timing information.
mainPatternVerify
    :: KoreIndexedModule
    -- ^ Module containing definitions visible in the pattern
    -> CommonKorePattern -- ^ Parsed pattern to check well-formedness
    -> IO ()
mainPatternVerify indexedModule patt =
    do
      verifyResult <-
        clockSomething "Verifying the pattern"
            ( verifyStandalonePattern indexedModule patt)
      case verifyResult of
        Left err1 -> error (printError err1)
        Right _   -> return ()

-- | IO action evaluates a Kore pattern and prints timing information.
mainEvaluatePattern
    :: KoreIndexedModule
    -- ^ Module containing definitions visible in the pattern
    -> CommonKorePattern -- ^ Parsed pattern to check well-formedness
    -> IO (FunctionResult Object)
mainEvaluatePattern indexedModule patt =
    clockSomethingIO "Evaluating the pattern" $
        evaluatePattern indexedModule patt

evaluatePattern
    :: KoreIndexedModule
    -- ^ Module containing definitions visible in the pattern
    -> CommonKorePattern -- ^ Parsed pattern to check well-formedness
    -> IO (FunctionResult Object)
evaluatePattern indexedModule patt = do
    purePattern <- case patternKoreToPure Object patt of
        Left err -> error (printError err)
        Right p  -> return p
    return
        (fst $ runIntCounter
            (evaluateFunctions
                (mockMetadataTools (extractMetadataTools indexedModule))
                (extractEvaluators Object conditionSort indexedModule)
                conditionSort
                purePattern
            )
            0
        )
  where
    conditionSort = SortVariableSort $ SortVariable
        (Id "ConditionSort" AstLocationConditionSortVariable)

extractEvaluators
    :: MetaOrObject level
    => level
    -> Sort level
    -> KoreIndexedModule
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
extractEvaluators level conditionSort indexedModule =
    Map.fromList (map extractPrefix groupedEvaluators)
  where
    extractPrefix []                  = error "unexpected case"
    extractPrefix ((a, b) : reminder) = (a, b : map snd reminder)
    groupedEvaluators =
        groupBy
            (\ (a, _) (c, _) -> a == c)
            (sortBy
                (comparing fst)
                (mapMaybe
                    (axiomToIdEvaluatorPair
                        level
                        (mockMetadataTools (extractMetadataTools indexedModule))
                        conditionSort
                    )
                    (indexedModuleAxioms indexedModule))
            )

axiomToIdEvaluatorPair
    :: MetaOrObject level
    => level
    -> MetadataTools level
    -> Sort level
    -> SentenceAxiom UnifiedSortVariable UnifiedPattern Variable
    -> Maybe (Id level, ApplicationFunctionEvaluator level)
axiomToIdEvaluatorPair
    level
    metadataTools
    conditionSort
    SentenceAxiom
        { sentenceAxiomParameters = [axiomSort]
        , sentenceAxiomPattern    = korePattern
        }
  = do
    purePattern <- case patternKoreToPure level korePattern of
        Left _  -> Nothing
        Right p -> return p
    (precondition, reminder) <- case fromPurePattern purePattern of
        ImpliesPattern Implies
            { impliesSort = SortVariableSort sort
            , impliesFirst = f
            , impliesSecond = s
            } -> do
                when (asUnified sort /= axiomSort) Nothing
                return (f, s)
        _ -> Nothing
    case fromPurePattern precondition of
        TopPattern _ -> return ()
        _            -> Nothing
    (postcondition, rule) <- case fromPurePattern reminder of
        AndPattern And {andFirst = f, andSecond = s} -> return (s, f)
        _                                            -> Nothing
    case fromPurePattern postcondition of
        TopPattern _ -> return ()
        _            -> Nothing
    (left, right) <- case fromPurePattern rule of
        EqualsPattern Equals {equalsFirst = f, equalsSecond = s} ->
            return (f, s)
        _ -> Nothing
    leftSymbol <- case fromPurePattern left of
        ApplicationPattern Application {applicationSymbolOrAlias = s} ->
            return s
        _ -> Nothing
    return
        ( symbolOrAliasConstructor leftSymbol
        , ApplicationFunctionEvaluator
            (axiomFunctionEvaluator
                metadataTools
                conditionSort
                AxiomPattern
                    { axiomPatternLeft  = left
                    , axiomPatternRight = right
                    }
            )
        )
axiomToIdEvaluatorPair _ _ _ _ = Nothing

mockMetadataTools :: MetadataTools level -> MetadataTools level
mockMetadataTools tools = MetadataTools
    { isConstructor = const True
    , isFunctional = const True
    , isFunction = const True
    , getArgumentSorts = getArgumentSorts tools
    , getResultSort = getResultSort tools
    }

prettyUnparseToString :: Unparse x => x -> String
prettyUnparseToString =
    filter (not . (\x -> isSpace x || x `elem` ['{','}'])) . unparseToString
