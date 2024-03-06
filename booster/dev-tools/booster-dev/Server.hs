{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (main) where

import Booster.Util (runHandleLoggingT)
import Control.Concurrent (newMVar)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (forM_, when)
import Control.Monad.Logger (runNoLoggingT)
import Control.Monad.Logger qualified as Log
import Control.Monad.Logger.CallStack (LogLevel (LevelError))
import Data.Conduit.Network (serverSettings)
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isNothing)
import Data.Text (Text, unpack)
import Options.Applicative
import System.IO qualified as IO

import Booster.CLOptions
import Booster.Definition.Base (KoreDefinition (..))
import Booster.Definition.Ceil (computeCeilsDefinition)
import Booster.GlobalState
import Booster.JsonRpc (ServerState (..), handleSmtError, respond)
import Booster.LLVM as LLVM (API)
import Booster.LLVM.Internal (mkAPI, withDLib)
import Booster.SMT.Interface qualified as SMT
import Booster.Syntax.ParsedKore (loadDefinition)
import Booster.Trace
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
            , llvmLibraryFile
            , smtOptions
            , equationOptions
            , eventlogEnabledUserEvents
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
        runServer port definitionMap mainModuleName mLlvmLibrary smtOptions (adjustLogLevels logLevels)
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
    Maybe SMT.SMTOptions ->
    (LogLevel, [LogLevel]) ->
    IO ()
runServer port definitions defaultMain mLlvmLibrary mSMTOptions (logLevel, customLevels) =
    do
        let logLevelToHandle = \case
                _ -> IO.stderr

        stateVar <-
            newMVar
                ServerState
                    { definitions
                    , defaultMain
                    , mLlvmLibrary
                    , mSMTOptions
                    , addedModules = mempty
                    }
        runHandleLoggingT logLevelToHandle . Log.filterLogger levelFilter $
            jsonRpcServer
                srvSettings
                (const $ respond stateVar)
                [handleSmtError, RpcError.handleErrorCall, RpcError.handleSomeException]
  where
    levelFilter _source lvl =
        lvl `elem` customLevels || lvl >= logLevel && lvl <= LevelError

    srvSettings = serverSettings port "*"
