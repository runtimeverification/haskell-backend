module Main (main) where

import Prelude.Kore

import Criterion.Main

import System.FilePath
    ( takeFileName
    )

import Kore.ASTVerifier.DefinitionVerifier
    ( verifyDefinition
    )
import qualified Kore.Builtin as Builtin
import Kore.Parser
    ( parseKoreDefinition
    )

import qualified Paths

main :: IO ()
main =
    defaultMain
    [ bgroup "Parse" (map parse koreFiles)
    , bgroup "Verify" (map verify (tail koreFiles))
    ]

{- | List of Kore files

The benchmarks in this module test parsing the following list of files.
-}
koreFiles :: [FilePath]
koreFiles =
    map Paths.dataFileName
    [ "../src/main/kore/prelude.kore"
    , "./test/resources/bool.kore"
    , "./test/resources/list.kore"
    , "./test/resources/nat.kore"
    ]

{- | Declare a parser benchmark

The benchmark will parse the contents of the file. The file is read only once
before the benchmark is run because Criterion may repeat a benchmark many times
to gather timing statistics.
-}
parse
    :: FilePath  -- ^ name of file to parse
    -> Benchmark
parse filename =
    env
        -- Read Kore definition once before benchmarkt
        (readFile filename)
        -- Benchmark parsing step only
        (bench name . nf (parseKoreDefinition filename))
  where
    name = takeFileName filename

{- | Declare a verifier benchmark

The benchmark will verify the contents of the file. The file is read and parsed
only once before the benchmark is run because Criterion may repeat a benchmark
many times to gather timing statistics.
-}
verify
    :: FilePath
    -> Benchmark
verify filename =
    env parse1 (bench name . nf verify1)
  where
    name = takeFileName filename
    -- | Read and parse the file once before the benchmark
    parse1 = do
        parsed <- parseKoreDefinition filename <$> readFile filename
        case parsed of
            Left err -> error err
            Right defn -> pure defn
    -- | Verify the Kore definition.
    -- Runs once per benchmark iteration.
    verify1 defn =
        case
            verifyDefinition Builtin.koreVerifiers defn
          of
            Left err -> error (show err)
            Right _ -> ()
