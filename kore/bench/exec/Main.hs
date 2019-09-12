module Main where

import Criterion.Main

import Data.Function
    ( (&)
    )
import Data.Limit
    ( Limit
    )
import qualified Data.Limit as Limit
import qualified Data.Map as Map
import qualified Data.Set as Set
import Numeric.Natural
    ( Natural
    )

import Kore.ASTVerifier.DefinitionVerifier
    ( AttributesVerification (DoNotVerifyAttributes)
    , verifyAndIndexDefinition
    )
import qualified Kore.ASTVerifier.PatternVerifier as PatternVerifier
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Symbol
import qualified Kore.Builtin as Builtin
import Kore.Error
    ( printError
    )
import Kore.Exec
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import qualified Kore.IndexedModule.IndexedModule as IndexedModule
import Kore.Internal.TermLike
    ( TermLike
    , Variable
    )
import Kore.Logger.Output
    ( emptyLogger
    )
import Kore.Parser
    ( parseKoreDefinition
    , parseKorePattern
    )
import Kore.Step
    ( anyRewrite
    )
import Kore.Syntax.Module
    ( ModuleName (..)
    )
import qualified SMT

import System.Directory
    ( removeFile
    )
import System.FilePath
    ( takeFileName
    , (</>)
    )
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
        execBenchmark root kFile definitionFile mainModuleName <$> testFiles

{- | List of Definitions to benchmark

The benchmarks in this module test each Definition in this list by benchmarking
each Definition's tests.
-}
definitions :: [Definition]
definitions =
    [ Definition
        { root =
            Paths.dataFileName
                "../src/main/k/working/function-evaluation-demo"
        , kFile = "demo.k"
        , definitionFile = "demo-kompiled/definition.kore"
        , mainModuleName = ModuleName "DEMO"
        , testFiles =
            [ "tests/Nat.demo"
            , "tests/NatList.demo"
            , "tests/Truth.demo"
            ]
        }
    , impDefinition "../src/main/k/working/imp-monosorted"
    , impDefinition "../src/main/k/working/imp-concrete-state"
    , impDefinition "../src/main/k/working/imp-concrete-heat-cool"
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
kBin = "../.build/k/k-distribution/target/release/k/bin"

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
    setUp :: IO
                ( VerifiedModule StepperAttributes Attribute.Axiom
                , TermLike Variable)
    setUp = do
        kompile
        definition <- readFile $ root </> definitionFile
        let
            parsedDefinition =
                either error id $ parseKoreDefinition "" definition
            verifiedModules =
                either (error . printError) id
                    $ verifyAndIndexDefinition
                        DoNotVerifyAttributes
                        Builtin.koreVerifiers
                        parsedDefinition
            Just verifiedModule = Map.lookup mainModuleName verifiedModules
        pat <- parseProgram
        let
            parsedPattern = either error id $ parseKorePattern "" pat
            verifiedPattern =
                either (error . printError) id
                $ PatternVerifier.runPatternVerifier context
                $ PatternVerifier.verifyStandalonePattern Nothing parsedPattern
              where
                context =
                    PatternVerifier.Context
                        { builtinDomainValueVerifiers =
                            Builtin.domainValueVerifiers Builtin.koreVerifiers
                        , indexedModule =
                            verifiedModule
                            & IndexedModule.eraseAxiomAttributes
                        , declaredSortVariables = Set.empty
                        , declaredVariables =
                            PatternVerifier.emptyDeclaredVariables
                        }
        return (verifiedModule, verifiedPattern)
    execution
        ::  ( VerifiedModule StepperAttributes Attribute.Axiom
            , TermLike Variable
            )
        -> IO (TermLike Variable)
    execution (verifiedModule, purePattern) =
        SMT.runSMT SMT.defaultConfig emptyLogger
        $ exec verifiedModule strategy purePattern
      where
        unlimited :: Limit Natural
        unlimited = Limit.Unlimited
        strategy = Limit.replicate unlimited . anyRewrite
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
