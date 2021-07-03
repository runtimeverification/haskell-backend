module Main (main) where

import Control.Monad (
    join,
 )
import Data.Map.Strict (
    elems,
 )
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
    ExitCode (ExitFailure, ExitSuccess),
    parseBugReportOption,
    withBugReport,
 )
import Kore.Equation (
    extractEquations,
    right,
 )
import Kore.Internal.TermLike (
    isFunctionPattern,
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

-- | modifiers for the command line parser description
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
    exitWith exitCode

koreCheckFunctions :: KoreCheckerOptions -> Main ExitCode
koreCheckFunctions opts = do
    definition <- loadDefinitions [fileName opts]
    mainModule <- loadModule (mainModuleName opts) definition
    let eqns = join $ elems $ extractEquations mainModule
    return $
        if all (isFunctionPattern . right) eqns
            then ExitSuccess
            else ExitFailure 2 -- What code should this be?
