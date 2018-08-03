module Main where

import Criterion.Main

import Kore.Parser.Parser
       ( fromKore )

import qualified Paths

main :: IO ()
main =
    defaultMain
    [ parse "kore.kore" (Paths.dataFileName "../../kore/kore.kore")
    , parse "bool.kore" (Paths.dataFileName "../../../test/resources/bool.kore")
    , parse "imp.kore" (Paths.dataFileName "../../../test/resources/imp.kore")
    , parse "imp2.kore" (Paths.dataFileName "../../../test/resources/imp2.kore")
    , parse "lambda.kore" (Paths.dataFileName "../../../test/resources/lambda.kore")
    , parse "list.kore" (Paths.dataFileName "../../../test/resources/list.kore")
    , parse "nat.kore" (Paths.dataFileName "../../../test/resources/nat.kore")
    , parse "user-meta-nat.kore" (Paths.dataFileName "../../../test/resources/user-meta-nat.kore")
    ]

{- | Declare a parser benchmark

The benchmark will parse the contents of the file. The file is read only once
before the benchmark is run because Criterion may repeat a benchmark many times
to gather timing statistics.
-}
parse
    :: String  -- ^ benchmark name (for the report)
    -> FilePath  -- ^ name of file to parse
    -> Benchmark
parse name filename =
    env (readFile filename)  -- Read Kore definition once before benchmark
    (bench name . nf (fromKore filename))  -- Benchmark parsing step only
