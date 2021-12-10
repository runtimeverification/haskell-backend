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

import Control.Monad.Catch (
    handle,
 )
import GlobalMain (
    ExeName (..),
    LocalOptions (..),
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
    checkFunctions,
 )
import Kore.Log (
    KoreLogOptions,
    parseKoreLogOptions,
    runKoreLog,
 )
import Kore.Log.ErrorException (
    handleSomeException,
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

-- | Executable name
exeName :: ExeName
exeName = ExeName "kore-check-functions"

-- | Environment variable name for extra arguments
envName :: String
envName = "KORE_CHECK_FUNCTIONS_OPTS"

main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <-
        mainGlobal
            exeName
            (Just envName) -- environment variable name for extra arguments
            (parseKoreCheckerOptions startTime)
            checkerInfoModifiers
    mapM_ mainWithOptions $ localOptions options

mainWithOptions :: LocalOptions KoreCheckerOptions -> IO ()
mainWithOptions localOptions@LocalOptions {execOptions} =
    withBugReport
        exeName
        (bugReportOption execOptions)
        (koreCheckFunctions localOptions)
        >>= exitWith

koreCheckFunctions :: LocalOptions KoreCheckerOptions -> FilePath -> IO ExitCode
koreCheckFunctions LocalOptions {execOptions, simplifierx} tmpDir =
    do
        definitions <- loadDefinitions [fileName]
        loadedModule <- loadModule mainModuleName definitions
        checkFunctions simplifierx loadedModule
            & SMT.runSMT defaultConfig (pure ())
        return ExitSuccess
        & handle handleSomeException
        & runKoreLog tmpDir koreLogOptions
  where
    KoreCheckerOptions
        { fileName
        , mainModuleName
        , koreLogOptions
        } = execOptions
