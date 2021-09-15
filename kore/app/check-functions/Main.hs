{- |
Copyright : (c) Runtime Verification, 2021
License   : BSD-3-Clause
-}
module Main (main) where

import GlobalMain (
    ExeName (..),
    Main,
    loadDefinitions,
    loadModule,
    localOptions,
    mainGlobal,
    parseModuleName,
 )
import Kore.BugReport (
    BugReportOption,
    ExitCode,
    parseBugReportOption,
    withBugReport,
 )
import Kore.Exec (
    checkFunctions,
    checkBothMatch,
 )
import Kore.Log (
    KoreLogOptions,
    parseKoreLogOptions,
    runKoreLog,
 )
import Kore.Options (
    InfoMod,
    Parser,
    argument,
    fullDesc,
    header,
    help,
    metavar,
    progDesc,
    str,
 )
import Kore.Syntax.Module (
    ModuleName,
 )
import Prelude.Kore
import SMT (
    runNoSMT,
 )
import System.Clock (
    Clock (Monotonic),
    TimeSpec,
    getTime,
 )
import System.Exit (
    exitWith,
 )
import Kore.Simplify.Data (evalSimplifier)

exeName :: ExeName
exeName = ExeName "kore-check-functions"

-- | Modifiers for the command line parser description
checkerInfoModifiers :: InfoMod options
checkerInfoModifiers =
    fullDesc
        <> progDesc
            "Checks function definitions in FILE and verifies that for every \
            \equation in a function definition, the right-hand side of the \
            \equation is a function pattern."
        <> header "kore-check-functions - a tool to check function definitions"

data KoreCheckerOptions = KoreCheckerOptions
    { -- | Name for a file containing function definitions to verify.
      fileName :: !FilePath
    , -- | Name of the main module in the definition
      mainModuleName :: !ModuleName
    , bugReportOption :: !BugReportOption
    , koreLogOptions :: !KoreLogOptions
    }

parseKoreCheckerOptions :: TimeSpec -> Parser KoreCheckerOptions
parseKoreCheckerOptions startTime =
    KoreCheckerOptions
        <$> argument
            str
            ( metavar "FILE"
                <> help "Kore source file to check."
            )
        <*> parseMainModuleName
        <*> parseBugReportOption
        <*> parseKoreLogOptions exeName startTime
  where
    parseMainModuleName =
        parseModuleName
            "MODULE"
            "module"
            "The name of the main module in the Kore definition."

main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <-
        mainGlobal
            exeName
            Nothing -- environment variable name for extra arguments
            (parseKoreCheckerOptions startTime)
            checkerInfoModifiers
    mapM_ mainWithOptions $ localOptions options

mainWithOptions :: KoreCheckerOptions -> IO ()
mainWithOptions opts = do
    exitCode <-
        withBugReport exeName (bugReportOption opts) $ \tmpDir ->
            koreCheckFunctions opts
                & runKoreLog tmpDir (koreLogOptions opts)
    exitCode' <-
        withBugReport exeName (bugReportOption opts) $ \tmpDir ->
            koreCheckBothMatch opts
                & runKoreLog tmpDir (koreLogOptions opts)
    exitWith $ max exitCode exitCode'

koreCheckBothMatch :: KoreCheckerOptions -> Main ExitCode
koreCheckBothMatch opts = do
    mod' <- loadDefinitions [fileName opts]
                >>= loadModule (mainModuleName opts)
    SMT.runNoSMT $ evalSimplifier mod' $ checkBothMatch mod' 
    
koreCheckFunctions :: KoreCheckerOptions -> Main ExitCode
koreCheckFunctions opts =
    loadDefinitions [fileName opts]
        >>= loadModule (mainModuleName opts)
        >>= checkFunctions
