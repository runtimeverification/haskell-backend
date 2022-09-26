{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Control.Monad.Catch (
    bracket,
    handle,
 )
import Control.Monad.Reader (
    ReaderT (..),
 )
import Data.IORef (writeIORef)
import Data.InternedText (globalInternedTextCache)
import GlobalMain qualified
import Kore.BugReport (
    BugReportOption,
    ExitCode,
    parseBugReportOption,
    withBugReport,
 )
import Kore.Exec (
    SerializedModule (..),
 )
import Kore.JsonRpc (runServer)
import Kore.Log (
    KoreLogOptions (..),
    parseKoreLogOptions,
    runKoreLog,
 )
import Kore.Log.ErrorException (
    handleSomeException,
 )
import Kore.Rewrite.SMT.Lemma (declareSMTLemmas)
import Kore.Syntax.Definition (
    ModuleName (..),
 )
import Log qualified
import Options.Applicative (
    InfoMod,
    Parser,
    argument,
    auto,
    fullDesc,
    header,
    help,
    long,
    metavar,
    option,
    str,
 )
import Options.SMT (
    KoreSolverOptions (..),
    ensureSmtPreludeExists,
    parseKoreSolverOptions,
 )
import Prelude.Kore
import SMT qualified
import System.Clock (
    Clock (Monotonic),
    TimeSpec,
    getTime,
 )
import System.Exit (
    ExitCode (ExitSuccess),
    exitWith,
 )

data KoreRpcServerOptions = KoreRpcServerOptions
    { definitionFileName :: !FilePath
    , mainModuleName :: !ModuleName
    , koreSolverOptions :: !KoreSolverOptions
    , koreLogOptions :: !KoreLogOptions
    , bugReportOption :: !BugReportOption
    , port :: !Int
    }

-- | Command Line Argument Parser
parseKoreRpcServerOptions :: TimeSpec -> Parser KoreRpcServerOptions
parseKoreRpcServerOptions startTime =
    KoreRpcServerOptions
        <$> argument
            str
            ( metavar "DEFINITION_FILE"
                <> help "Kore definition file to verify and use for execution"
            )
        <*> parseMainModuleName
        <*> parseKoreSolverOptions
        <*> parseKoreLogOptions Main.exeName startTime
        <*> parseBugReportOption
        <*> option
            auto
            ( metavar "SERVER_PORT"
                <> long "server-port"
                <> help "Port for the RPC server to bind to"
            )
  where
    parseMainModuleName =
        GlobalMain.parseModuleName
            "MODULE"
            "module"
            "The name of the main module in the Kore definition."

-- | modifiers for the Command line parser description
parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> header "kore-rpc - a JSON RPC server for symbolically executing Kore definitions"

exeName :: GlobalMain.ExeName
exeName = GlobalMain.ExeName "kore-rpc"

-- | Environment variable name for extra arguments
envName :: String
envName = "KORE_RPC_OPTS"

main :: IO ()
main = do
    startTime <- getTime Monotonic
    options <-
        GlobalMain.mainGlobal
            Main.exeName
            (Just envName)
            (parseKoreRpcServerOptions startTime)
            parserInfoModifiers
    for_ (GlobalMain.localOptions options) mainWithOptions

mainWithOptions :: GlobalMain.LocalOptions KoreRpcServerOptions -> IO ()
mainWithOptions localOptions@GlobalMain.LocalOptions{execOptions = KoreRpcServerOptions{koreSolverOptions, koreLogOptions, bugReportOption}} = do
    ensureSmtPreludeExists koreSolverOptions
    exitWith
        =<< withBugReport
            Main.exeName
            bugReportOption
            ( \tmpDir ->
                koreRpcServerRun localOptions
                    & handle handleSomeException
                    & runKoreLog
                        tmpDir
                        koreLogOptions
            )

koreRpcServerRun ::
    GlobalMain.LocalOptions KoreRpcServerOptions ->
    GlobalMain.Main ExitCode
koreRpcServerRun GlobalMain.LocalOptions{execOptions} = do
    GlobalMain.SerializedDefinition{serializedModule, lemmas, internedTextCache} <-
        GlobalMain.deserializeDefinition
            koreSolverOptions
            definitionFileName
            mainModuleName
    lift $ writeIORef globalInternedTextCache internedTextCache

    let SerializedModule{metadataTools} = serializedModule

    -- initialize an SMT solver with user declared lemmas
    let setupSolver smtSolverRef = do
            let userInit = SMT.runWithSolver $ declareSMTLemmas metadataTools lemmas
            let solverSetup = SMT.SolverSetup{userInit, refSolverHandle = smtSolverRef, config = smtConfig}
            SMT.initSolver solverSetup
            return solverSetup

    -- launch the SMT solver, initialize it and then pass the SolverSetup object to the RPC server
    GlobalMain.clockSomethingIO "Executing" $
        bracket
            (SMT.newSolver smtConfig >>= setupSolver)
            (SMT.stopSolver . SMT.refSolverHandle)
            $ \solverSetup -> do
                -- wrap the call to runServer in the logger monad
                Log.LoggerT $ ReaderT $ \loggerEnv -> runServer port solverSetup loggerEnv serializedModule

    pure ExitSuccess
  where
    KoreRpcServerOptions{definitionFileName, mainModuleName, koreSolverOptions, port} = execOptions
    KoreSolverOptions{timeOut, rLimit, resetInterval, prelude} = koreSolverOptions
    smtConfig =
        SMT.defaultConfig
            { SMT.timeOut = timeOut
            , SMT.rLimit = rLimit
            , SMT.resetInterval = resetInterval
            , SMT.prelude = prelude
            }
