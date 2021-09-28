{- |
Copyright : (c) Runtime Verification, 2021
License   : BSD-3-Clause

The @kore-check-functions@ executable checks the following properties of
function definitions:
1. For every equation in a function definition, the right-hand side of the
equation is a function pattern.
2. For every pair of equations in a function definition, the equations cannot
match the same term.
-}
module Main (main) where

import GlobalMain (
    ExeName (..),
    LoadedModule,
    Main,
    loadDefinitions,
    loadModule,
    localOptions,
    mainGlobal,
    parseModuleName,
 )
import Kore.BugReport (
    BugReportOption,
    ExitCode (..),
    parseBugReportOption,
    withBugReport,
 )
import Kore.Exec (
    checkBothMatch,
    checkFunctions,
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
import Kore.Simplify.Data (evalSimplifier)
import Kore.Syntax.Module (
    ModuleName,
 )
import Prelude.Kore
import SMT (
    defaultConfig,
    runSMT,
 )
import System.Clock (
    Clock (Monotonic),
    TimeSpec,
    getTime,
 )
import System.Exit (
    exitWith,
 )

exeName :: ExeName
exeName = ExeName "kore-check-functions"

-- | Modifiers for the command line parser description
checkerInfoModifiers :: InfoMod options
checkerInfoModifiers =
    fullDesc
        <> progDesc
            "Checks function definitions in FILE and verifies the following \
            \properties: \
            \1. For every equation in a function definition, the right-hand \
            \side of the equation is a function pattern. \
            \2. For every pair of equations in a function definition, the \
            \equations cannot match the same term."
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
    exitCode <- withBugReport' koreCheckFunctions
    case exitCode of
        ExitFailure _ -> exitWith exitCode
        ExitSuccess ->
            withBugReport' koreCheckBothMatch
                >>= exitWith
  where
    withBugReport' check =
        withBugReport exeName (bugReportOption opts) $ \tmpDir ->
            getLoadedModule opts >>= check
                & runKoreLog tmpDir (koreLogOptions opts)

getLoadedModule :: KoreCheckerOptions -> Main LoadedModule
getLoadedModule opts =
    loadDefinitions [fileName opts]
        >>= loadModule (mainModuleName opts)

koreCheckBothMatch :: LoadedModule -> Main ExitCode
koreCheckBothMatch loadedMod =
    SMT.runSMT defaultConfig (pure ()) $ evalSimplifier loadedMod $ checkBothMatch loadedMod

koreCheckFunctions :: LoadedModule -> Main ExitCode
koreCheckFunctions = checkFunctions
