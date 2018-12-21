module Main where

import Criterion.Main

import qualified Control.Lens as Lens
import           Data.Function
                 ( (&) )
import           Data.Limit
                 ( Limit (Unlimited) )
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Kore.AST.Kore as Kore
import           Kore.AST.Pure
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.AST.Sentence
                 ( ModuleName (..) )
import           Kore.ASTVerifier.DefinitionVerifier
                 ( AttributesVerification (DoNotVerifyAttributes),
                 verifyAndIndexDefinition )
import qualified Kore.ASTVerifier.PatternVerifier as PatternVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( printError )
import           Kore.Exec
import           Kore.IndexedModule.IndexedModule
                 ( IndexedModule (..), VerifiedModule,
                 mapIndexedModulePatterns )
import           Kore.Parser.Parser
                 ( fromKore, fromKorePattern )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Step.Step
                 ( anyRewrite )
import           Kore.Step.StepperAttributes
import qualified SMT

import           System.Directory
                 ( removeFile )
import           System.FilePath
                 ( takeFileName, (</>) )
import qualified System.Process as Proc

import qualified Paths

{- | An example K definition along with test programs -}
data Definition = Definition
    { root :: !FilePath
    , kFile :: !FilePath
    , definitionFile :: !FilePath
    , mainModuleName :: !ModuleName
    , testFiles :: ![FilePath]
    }

main :: IO ()
main = defaultMain groups
  where
    groups = group <$> definitions

group :: Definition -> Benchmark
group
    Definition
        { root
        , kFile
        , definitionFile
        , mainModuleName
        , testFiles }
  =
    bgroup (takeFileName root) tests
  where
    tests =
        (execBenchmark root kFile definitionFile mainModuleName) <$> testFiles

{- | List of Definitions to benchmark

The benchmarks in this module test each Definition in this list by benchmarking
each Definition's tests.
-}
definitions :: [Definition]
definitions =
    [ Definition
        { root = Paths.dataFileName "../../k/working/function-evaluation-demo"
        , kFile = "demo.k"
        , definitionFile = "demo-kompiled/definition.kore"
        , mainModuleName = ModuleName "DEMO"
        , testFiles =
            [ "tests/Nat.demo"
            , "tests/NatList.demo"
            , "tests/Truth.demo"
            ]
        }
    , impDefinition "../../k/working/imp-monosorted"
    , impDefinition "../../k/working/imp-concrete-state"
    , impDefinition "../../k/working/imp-concrete-heat-cool"
    ]
  where
    impDefinition root = Definition
        { root = Paths.dataFileName root
        , kFile = "imp.k"
        , mainModuleName = ModuleName "IMP"
        , definitionFile = "imp-kompiled/definition.kore"
        , testFiles =
            [ "tests/collatz.imp"
            , "tests/primes.imp"
            , "tests/sum.imp"
            ]
        }

{- | Path to the directory containing kompile, kast, and krun -}
kBin :: FilePath
kBin = "../../../../.build/k/k-distribution/target/release/k/bin"

{- | Declare an execution benchmark

Before Criterion starts timing, kompile the K definition and parse the input
program into a kore pattern. Then each benchmark times concrete execution
alone.
-}
execBenchmark
    :: FilePath
    -> FilePath
    -> FilePath
    -> ModuleName
    -> FilePath
    -> Benchmark
execBenchmark root kFile definitionFile mainModuleName test =
    envWithCleanup setUp cleanUp $ bench name . nfIO . execution
  where
    name = takeFileName test
    setUp :: IO (VerifiedModule StepperAttributes, CommonStepPattern Object)
    setUp = do
        kompile
        definition <- readFile $ root </> definitionFile
        let
            parsedDefinition = either error id $ fromKore "" definition
            verifiedModules =
                either (error . printError) id
                    $ verifyAndIndexDefinition
                        DoNotVerifyAttributes
                        Builtin.koreVerifiers
                        parsedDefinition
            Just verifiedModule =
                fmap constructorFunctions
                    $ Map.lookup mainModuleName verifiedModules
            indexedModule =
                mapIndexedModulePatterns
                    Kore.eraseAnnotations
                    verifiedModule
        pat <- parseProgram
        let
            parsedPattern = either error id $ fromKorePattern "" pat
            verifiedPattern =
                either (error . printError) id
                $ PatternVerifier.runPatternVerifier context
                $ PatternVerifier.verifyStandalonePattern Nothing parsedPattern
              where
                context =
                    PatternVerifier.Context
                        { builtinPatternVerifier =
                            Builtin.patternVerifier Builtin.koreVerifiers
                        , indexedModule = Attribute.Null <$ indexedModule
                        , declaredSortVariables = Set.empty
                        , declaredVariables =
                            PatternVerifier.emptyDeclaredVariables
                        }
            purePattern =
                either (error . printError) id
                $ patternKoreToPure Object verifiedPattern
        return (verifiedModule, purePattern)
    execution
        :: (VerifiedModule StepperAttributes, CommonStepPattern Object)
        -> IO (CommonStepPattern Object)
    execution (verifiedModule, purePattern) =
        SMT.runSMT SMT.defaultConfig
        $ evalSimplifier
        $ exec verifiedModule purePattern Unlimited anyRewrite
    kompile = myShell $ (kBin </> "kompile")
        ++ " --backend haskell -d " ++ root
        ++ " " ++ (root </> kFile)
    patternKoreFile = (root </> test) ++ ".kore"
    parseProgram = do
        myShell $ (kBin </> "krun")
            ++ " -d " ++ root ++ " --dry-run " ++ (root </> test)
        readFile patternKoreFile
    cleanUp _ = removeFile patternKoreFile
    quiet p = p { Proc.std_out = Proc.NoStream, Proc.std_err = Proc.NoStream }
    myShell command = do
        (_, _, _, ph) <- Proc.createProcess $ quiet $ Proc.shell command
        _ <- Proc.waitForProcess ph
        return ()

-- TODO (traiansf): Get rid of this.
-- The function below works around several limitations of
-- the current tool by tricking the tool into believing that
-- functions are constructors (so that function patterns can match)
-- and that @kseq@ and @dotk@ are both functional and constructor.
constructorFunctions
    :: IndexedModule sortParam patternType StepperAttributes
    -> IndexedModule sortParam patternType StepperAttributes
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
    constructorFunctions1 ident (atts, defn) =
        ( atts
            & lensConstructor Lens.<>~ Constructor isCons
            & lensFunctional Lens.<>~ Functional (isCons || isInj)
            & lensInjective Lens.<>~ Injective (isCons || isInj)
            & lensSortInjection Lens.<>~ SortInjection isInj
        , defn
        )
      where
        isInj = getId ident == "inj"
        isCons = elem (getId ident) ["kseq", "dotk"]

    recurseIntoImports (attrs, attributes, importedModule) =
        (attrs, attributes, constructorFunctions importedModule)
