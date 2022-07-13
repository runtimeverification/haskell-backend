{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Control.Monad.Catch (
    bracket,
    handle,
 )
import Control.Monad.Reader (
    ReaderT (..),
 )


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
    metavar,
    str,
    long,
    option,
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
    -- , version :: _ ??
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

-- main :: IO ()
-- main = runServer 31337

mainWithOptions :: GlobalMain.LocalOptions KoreRpcServerOptions -> IO ()
mainWithOptions localOptions@GlobalMain.LocalOptions{execOptions = KoreRpcServerOptions{koreSolverOptions, koreLogOptions, bugReportOption}} = do
    ensureSmtPreludeExists koreSolverOptions
    exitWith
        =<< ( withBugReport Main.exeName bugReportOption $ \tmpDir ->
                koreRpcServerRun localOptions
                    & handle handleSomeException
                    & runKoreLog
                        tmpDir
                        koreLogOptions
            )

koreRpcServerRun :: GlobalMain.LocalOptions KoreRpcServerOptions -> GlobalMain.Main ExitCode
koreRpcServerRun GlobalMain.LocalOptions{execOptions, simplifierx} = do
    let KoreRpcServerOptions{definitionFileName, mainModuleName, koreSolverOptions, port} = execOptions
        KoreSolverOptions{timeOut, rLimit, resetInterval, prelude} = koreSolverOptions
    GlobalMain.SerializedDefinition{serializedModule, lemmas} <-
        GlobalMain.deserializeDefinition simplifierx koreSolverOptions definitionFileName mainModuleName
    let SerializedModule{metadataTools} = serializedModule
    let smtConfig =
            SMT.defaultConfig
                { SMT.timeOut = timeOut
                , SMT.rLimit = rLimit
                , SMT.resetInterval = resetInterval
                , SMT.prelude = prelude
                }

    GlobalMain.clockSomethingIO "Executing" $
        bracket
            (SMT.newSolver smtConfig)
            SMT.stopSolver
            $ \mvar -> do
                let solverSetup = SMT.SolverSetup{userInit = declareSMTLemmas metadataTools lemmas, refSolverHandle = mvar, config = smtConfig}
                runReaderT (SMT.getSMT SMT.initSolver) solverSetup
                Log.LoggerT $ ReaderT $ \loggerEnv -> runServer port solverSetup loggerEnv simplifierx serializedModule

    pure ExitSuccess

-- exec ::
--     forall smt.
--     ( MonadIO smt
--     , MonadLog smt
--     , MonadSMT smt
--     , MonadMask smt
--     , MonadProf smt
--     ) =>
--     SimplifierXSwitch ->
--     Limit Natural ->
--     Limit Natural ->
--     -- | The main module
--     SerializedModule ->
--     ExecutionMode ->
--     -- | The input pattern
--     TermLike VariableName ->
--     smt (ExitCode, TermLike VariableName)
-- exec
--     simplifierx
--     depthLimit
--     breadthLimit
--     SerializedModule
--         { sortGraph
--         , overloadGraph
--         , metadataTools
--         , verifiedModule
--         , rewrites
--         , equations
--         }
--     strategy
--     (mkRewritingTerm -> initialTerm) =
--         evalSimplifier simplifierx verifiedModule' sortGraph overloadGraph metadataTools equations $ do
--             let Initialized{rewriteRules} = rewrites
--             finals <-
--                 getFinalConfigsOf $ do
--                     initialConfig <-
--                         Pattern.simplify
--                             (Pattern.fromTermLike initialTerm)
--                             >>= Logic.scatter
--                     let updateQueue = \as ->
--                             Strategy.unfoldDepthFirst as
--                                 >=> lift
--                                     . Strategy.applyBreadthLimit
--                                         breadthLimit
--                                         dropStrategy
--                         rewriteGroups = groupRewritesByPriority rewriteRules
--                         transit instr config =
--                             Strategy.transitionRule
--                                 ( transitionRule rewriteGroups strategy
--                                     & profTransitionRule
--                                     & trackExecDepth
--                                 )
--                                 instr
--                                 config
--                                 & runTransitionT
--                                 & fmap (map fst)
--                                 & lift
--                     Strategy.leavesM
--                         Leaf
--                         updateQueue
--                         (unfoldTransition transit)
--                         ( limitedExecutionStrategy depthLimit
--                         , (ExecDepth 0, Start initialConfig)
--                         )
--             let (depths, finalConfigs) = unzip finals
--             infoExecDepth (maximum (ExecDepth 0 : depths))
--             let finalConfigs' =
--                     MultiOr.make $
--                         mapMaybe extractProgramState finalConfigs
--             exitCode <- getExitCode verifiedModule finalConfigs'
--             let finalTerm =
--                     MultiOr.map getRewritingPattern finalConfigs'
--                         & OrPattern.toTermLike initialSort
--                         & sameTermLikeSort initialSort
--             return (exitCode, finalTerm)
--       where
--         dropStrategy = snd
--         getFinalConfigsOf act = observeAllT $ fmap snd act
--         verifiedModule' =
--             IndexedModule.mapAliasPatterns
--                 -- TODO (thomas.tuegel): Move this into Kore.Builtin
--                 (Builtin.internalize metadataTools)
--                 verifiedModule
--         initialSort = termLikeSort initialTerm
--         unfoldTransition transit (instrs, config) = do
--             when (null instrs) $ forM_ depthLimit warnDepthLimitExceeded
--             Strategy.unfoldTransition transit (instrs, config)
