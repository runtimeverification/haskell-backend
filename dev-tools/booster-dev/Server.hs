{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (main) where

import Control.Concurrent (newMVar)
import Control.DeepSeq (force)
import Control.Exception (evaluate)
import Control.Monad (when)
import Control.Monad.Logger (runNoLoggingT)
import Control.Monad.Logger qualified as Log
import Control.Monad.Logger.CallStack (LogLevel)
import Control.Monad.Trans.Reader (runReaderT)
import Data.Conduit.Network (serverSettings)
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, isNothing)
import Data.Text (Text, unpack)
import Data.Text.Encoding qualified as Text
import Options.Applicative

import Booster.CLOptions
import Booster.Definition.Base (KoreDefinition (..))
import Booster.Definition.Ceil (computeCeilsDefinition)
import Booster.GlobalState
import Booster.JsonRpc (ServerState (..), handleSmtError, respond)
import Booster.LLVM as LLVM (API)
import Booster.LLVM.Internal (mkAPI, withDLib)
import Booster.Log qualified
import Booster.Log.Context qualified as Booster.Log
import Booster.Pattern.Pretty
import Booster.SMT.Interface qualified as SMT
import Booster.Syntax.ParsedKore (loadDefinition)
import Booster.Util (
    newTimeCache,
    withFastLogger,
    pattern NoPrettyTimestamps,
    pattern PrettyTimestamps,
 )
import Booster.Util qualified as Booster
import Kore.JsonRpc.Error qualified as RpcError
import Kore.JsonRpc.Server

main :: IO ()
main = do
    options <- execParser clParser
    let CLOptions
            { definitionFile
            , mainModuleName
            , llvmLibraryFile
            , port
            , logOptions =
                LogOptions
                    { logLevels
                    , logContexts
                    , logTimeStamps
                    , timeStampsFormat
                    , logFormat
                    , logFile
                    , prettyPrintOptions
                    }
            , smtOptions
            , equationOptions
            , rewriteOptions
            } = options

    putStrLn $
        "Loading definition from "
            <> definitionFile
            <> ", main module "
            <> show mainModuleName

    withLlvmLib llvmLibraryFile $ \mLlvmLibrary -> do
        definitionMap <-
            loadDefinition rewriteOptions.indexCells definitionFile
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
            rewriteOptions
            logFile
            smtOptions
            (adjustLogLevels logLevels)
            logContexts
            logTimeStamps
            timeStampsFormat
            logFormat
            prettyPrintOptions
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
    RewriteOptions ->
    Maybe FilePath ->
    Maybe SMT.SMTOptions ->
    (LogLevel, [LogLevel]) ->
    [Booster.Log.ContextFilter] ->
    Bool ->
    TimestampFormat ->
    LogFormat ->
    [ModifierT] ->
    IO ()
runServer port definitions defaultMain mLlvmLibrary rewriteOpts logFile mSMTOptions (_logLevel, customLevels) logContexts logTimeStamps timeStampsFormat logFormat prettyPrintOptions =
    do
        let timestampFlag = case timeStampsFormat of
                Pretty -> PrettyTimestamps
                Nanoseconds -> NoPrettyTimestamps
        mTimeCache <- if logTimeStamps then Just <$> newTimeCache timestampFlag else pure Nothing

        withFastLogger mTimeCache logFile $ \stderrLogger mFileLogger -> do
            let boosterContextLogger = case logFormat of
                    Json -> Booster.Log.jsonLogger $ fromMaybe stderrLogger mFileLogger
                    _ -> Booster.Log.textLogger $ fromMaybe stderrLogger mFileLogger
                filteredBoosterContextLogger =
                    flip Booster.Log.filterLogger boosterContextLogger $ \(Booster.Log.LogMessage (Booster.Flag alwaysDisplay) ctxts _) ->
                        alwaysDisplay
                            || let ctxt = map (Text.encodeUtf8 . Booster.Log.toTextualLog) ctxts
                                in any (flip Booster.Log.mustMatch ctxt) $
                                    logContexts
                                        <> concatMap (\case Log.LevelOther o -> fromMaybe [] $ levelToContext Map.!? o; _ -> []) customLevels
            stateVar <-
                newMVar
                    ServerState
                        { definitions
                        , defaultMain
                        , mLlvmLibrary
                        , mSMTOptions
                        , rewriteOptions = rewriteOpts
                        , addedModules = mempty
                        }
            jsonRpcServer
                (serverSettings port "*")
                (isJust mLlvmLibrary) -- run in bound threads if LLVM library in use
                ( \rawReq req ->
                    flip runReaderT (filteredBoosterContextLogger, toModifiersRep prettyPrintOptions)
                        . Booster.Log.unLoggerT
                        . Booster.Log.withContextFor (getReqId rawReq)
                        . Booster.Log.withContext Booster.Log.CtxBooster
                        . respond stateVar
                        $ req
                )
                [handleSmtError, RpcError.handleErrorCall, RpcError.handleSomeException]
