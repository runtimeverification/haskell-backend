module Main where

import Criterion.Main

import System.Directory
       ( removeFile )
import System.FilePath
       ( takeFileName, (</>) )
import System.IO.Temp
       ( writeSystemTempFile )
import qualified System.Process as Proc

import qualified Paths

{- | An example K definition along with test programs -}
data Definition = Definition
    { root :: !FilePath
    , kFile :: !FilePath
    , testFiles :: ![FilePath]
    }

main :: IO ()
main = defaultMain 
    [ bgroup 
        (takeFileName root) 
        [ exec root kFile test |  test <- testFiles ] 
    | Definition { root, kFile, testFiles } <- definitions
    ]

{- | List of Definitions to benchmark

The benchmarks in this module test each Definition in this list by benchmarking
each Definition's tests.
-}
definitions :: [Definition]
definitions =
    [ Definition 
        { root = Paths.dataFileName "../../k/working/function-evaluation-demo"
        , kFile = "demo.k"
        , testFiles = 
            [ "tests/Nat.demo"
            , "tests/NatList.demo"
            , "tests/Truth.demo"
            ]
        }
    , Definition
        { root = Paths.dataFileName "../../k/working/imp-monosorted"
        , kFile = "imp.k"
        , testFiles = impTests
        }
    , Definition
        { root = Paths.dataFileName "../../k/working/imp-concrete-state"
        , kFile = "imp.k"
        , testFiles = impTests
        }
    , Definition
        { root = Paths.dataFileName "../../k/working/imp-concrete-heat-cool"
        , kFile = "imp.k"
        , testFiles = impTests
        }
    ]
  where 
    impTests =
        [ "tests/collatz.imp"
        , "tests/max-symbolic.imp"
        , "tests/primes.imp"
        , "tests/sum.imp"
        ]

{- | Path to the directory containing kompile, kast, and krun -}
kBin :: FilePath
kBin = "../../../../.build/k/k-distribution/target/release/k/bin"

{- | Declare an execution benchmark

Before Criterion starts timing, kompile the K definition and kast the program
into a temporary file. Then each benchmark times krun without kast.
-}
exec
    :: FilePath
    -> FilePath
    -> FilePath
    -> Benchmark
exec root kFile test = envWithCleanup setUp cleanUp $ bench name . nfIO . krun
  where
    name = takeFileName test
    setUp = do
        kompile
        kastFile <- writeKast
        koreExec <- getKoreExec
        return (koreExec, kastFile)
    cleanUp (_, kastFile) = removeFile kastFile
    krun (koreExec, kastFile) = myShell $ (kBin </> "krun") 
        ++ " --haskell-backend-command \"" ++ koreExec ++ "\" -d " ++ root 
        ++ " --parser cat " ++ kastFile
    kompile = myShell $ (kBin </> "kompile") 
        ++ " --backend haskell -d " ++ root
        ++ " " ++ (root </> kFile)
    writeKast = do
        let kastProc = Proc.proc (kBin </> "kast") ["-d", root, (root </> test)]
        kast <- Proc.readCreateProcess (quiet kastProc) ""
        writeSystemTempFile "kast" kast 
    getKoreExec = do
        let command = "stack path --local-install-root"
        [stackRoot] <- lines <$> Proc.readCreateProcess (Proc.shell command) ""
        return $ stackRoot </> "bin" </> "kore-exec"
    quiet p = p { Proc.std_out = Proc.NoStream, Proc.std_err = Proc.NoStream }
    myShell command = do
        (_, _, _, ph) <- Proc.createProcess $ quiet $ Proc.shell command
        _ <- Proc.waitForProcess ph
        return ()
