{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (main) where

import Booster.Util (handleOutput, withFastLogger)
import Control.Concurrent (newMVar)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_, when)
import Control.Monad.Logger (runNoLoggingT)
import Control.Monad.Logger qualified as Log
import Control.Monad.Logger.CallStack (LogLevel (LevelError))
import Control.Monad.Trans.Reader (runReaderT)
import Data.Conduit.Network (serverSettings)
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Text (Text, unpack)
import Options.Applicative
import System.FilePath.Glob qualified as Glob
import System.Log.FastLogger (newTimeCache)

import Booster.CLOptions
import Booster.Definition.Base (KoreDefinition (..))
import Booster.Definition.Ceil (computeCeilsDefinition)
import Booster.GlobalState
import Booster.JsonRpc (ServerState (..), handleSmtError, respond)
import Booster.LLVM as LLVM (API)
import Booster.LLVM.Internal (mkAPI, withDLib)
import Booster.Log qualified
import Booster.SMT.Interface qualified as SMT
import Booster.Syntax.ParsedKore (loadDefinition)
import Booster.Trace
import Data.Text qualified as Text
import Kore.JsonRpc.Error qualified as RpcError
import Kore.JsonRpc.Server

main :: IO ()
main = do
    options <- execParser clParser
    let CLOptions
            { definitionFile
            , mainModuleName
            , port
            , logLevels
            , logContexts
            , notLogContexts
            , logTimeStamps
            , logFormat
            , llvmLibraryFile
            , smtOptions
            , equationOptions
            , eventlogEnabledUserEvents
            , simplificationLogFile
            } = options

    forM_ eventlogEnabledUserEvents $ \t -> do
        putStrLn $ "Tracing " <> show t
        enableCustomUserEvent t
    putStrLn $
        "Loading definition from "
            <> definitionFile
            <> ", main module "
            <> show mainModuleName

    withLlvmLib llvmLibraryFile $ \mLlvmLibrary -> do
        definitionMap <-
            loadDefinition definitionFile
                >>= mapM (mapM ((fst <$>) . runNoLoggingT . computeCeilsDefinition mLlvmLibrary))
                >>= evaluate . force . either (error . show) id
        -- ensure the (default) main module is present in the definition
        when (isNothing $ Map.lookup mainModuleName definitionMap) $
            error $
                "Module " <> unpack mainModuleName <> " does not exist in the given definition."

        writeGlobalEquationOptions equationOptions

        putStrLn "Starting RPC server"
        runServer
            port
            definitionMap
            mainModuleName
            mLlvmLibrary
            simplificationLogFile
            smtOptions
            (adjustLogLevels logLevels)
            logContexts
            notLogContexts
            logTimeStamps
            logFormat
  where
    withLlvmLib libFile m = case libFile of
        Nothing -> m Nothing
        Just fp -> withDLib fp $ \dl -> do
            api <- mkAPI dl
            m $ Just api

    clParser =
        info
            (clOptionsParser <**> versionInfoParser <**> helper)
            parserInfoModifiers

parserInfoModifiers :: InfoMod options
parserInfoModifiers =
    fullDesc
        <> header
            "Haskell Backend Booster - a JSON RPC server for quick symbolic execution of Kore definitions"

runServer ::
    Int ->
    Map Text KoreDefinition ->
    Text ->
    Maybe LLVM.API ->
    Maybe FilePath ->
    Maybe SMT.SMTOptions ->
    (LogLevel, [LogLevel]) ->
    [String] ->
    [String] ->
    Bool ->
    LogFormat ->
    IO ()
runServer port definitions defaultMain mLlvmLibrary simplificationLogFile mSMTOptions (logLevel, customLevels) logContexts notLogContexts logTimeStamps logFormat =
    do
        mTimeCache <- if logTimeStamps then Just <$> (newTimeCache "%Y-%m-%d %T") else pure Nothing

        withFastLogger mTimeCache simplificationLogFile $ \stderrLogger mFileLogger -> do
            let boosterContextLogger = case logFormat of
                    Json -> Booster.Log.jsonLogger $ fromMaybe stderrLogger mFileLogger
                    _ -> Booster.Log.textLogger stderrLogger
                filteredBoosterContextLogger =
                    flip Booster.Log.filterLogger boosterContextLogger $ \(Booster.Log.LogMessage ctxts _) ->
                        let ctxt = unwords $ map (\(Booster.Log.LogContext lc) -> Text.unpack $ Booster.Log.toTextualLog lc) ctxts
                         in not (any (flip Glob.match ctxt) negGlobPatterns)
                                && any (flip Glob.match ctxt) globPatterns
            stateVar <-
                newMVar
                    ServerState
                        { definitions
                        , defaultMain
                        , mLlvmLibrary
                        , mSMTOptions
                        , addedModules = mempty
                        }
            flip Log.runLoggingT (handleOutput stderrLogger mFileLogger) . Log.filterLogger levelFilter $
                jsonRpcServer
                    srvSettings
                    ( const $
                        flip runReaderT filteredBoosterContextLogger
                            . Booster.Log.unLoggerT
                            . respond stateVar
                    )
                    [handleSmtError, RpcError.handleErrorCall, RpcError.handleSomeException]
  where
    globPatterns = map (Glob.compile . filter (\c -> not (c == '\'' || c == '"'))) logContexts
    negGlobPatterns = map (Glob.compile . filter (\c -> not (c == '\'' || c == '"'))) notLogContexts
    levelFilter :: Log.LogSource -> LogLevel -> Bool
    levelFilter _source lvl =
        lvl `elem` customLevels
            || case lvl of
                Log.LevelOther l ->
                    not (any (flip Glob.match (Text.unpack l)) negGlobPatterns)
                        && any (flip Glob.match (Text.unpack l)) globPatterns
                _ -> False
            || lvl >= logLevel && lvl <= LevelError
    srvSettings = serverSettings port "*"
