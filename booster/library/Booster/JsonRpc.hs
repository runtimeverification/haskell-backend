{-# LANGUAGE FlexibleContexts #-}

{- |
Module      : Booster.JsonRpc
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.JsonRpc (
    module Booster.JsonRpc,
    rpcJsonConfig,
) where

import Control.Concurrent (MVar, newMVar, putMVar, readMVar, takeMVar)
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Logger.CallStack (LogLevel (LevelError), MonadLoggerIO)
import Control.Monad.Logger.CallStack qualified as Log
import Control.Monad.Trans.Except (runExcept, throwE)
import Data.Conduit.Network (serverSettings)
import Data.Foldable
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Records
import Numeric.Natural

import Booster.Definition.Base (KoreDefinition (..))
import Booster.LLVM.Internal qualified as LLVM
import Booster.Pattern.Base (Pattern)
import Booster.Pattern.Rewrite (RewriteResult (..), performRewrite)
import Booster.Syntax.Json (KoreJson (..), addHeader)
import Booster.Syntax.Json.Externalise (externalisePattern)
import Booster.Syntax.Json.Internalise (internalisePattern)
import Booster.Syntax.ParsedKore (parseKoreModule)
import Booster.Syntax.ParsedKore.Base
import Booster.Syntax.ParsedKore.Internalise (DefinitionError (..), addToDefinitions)
import Kore.JsonRpc.Error
import Kore.JsonRpc.Server
import Kore.JsonRpc.Types
import Kore.Syntax.Json.Types (Id (..))

respond ::
    forall m.
    MonadLoggerIO m =>
    MVar ServerState ->
    Respond (API 'Req) m (API 'Res)
respond stateVar =
    \case
        Execute req
            | isJust req.stepTimeout -> pure $ Left $ unsupportedOption ("step-timeout" :: String)
            | isJust req.movingAverageStepTimeout -> pure $ Left $ unsupportedOption ("moving-average-step-timeout" :: String)
        Execute req -> withContext req._module $ \(def, mLlvmLibrary) -> do
            -- internalise given constrained term
            let internalised = runExcept $ internalisePattern Nothing def req.state.term

            case internalised of
                Left patternError -> do
                    Log.logDebug $ "Error internalising cterm" <> Text.pack (show patternError)
                    pure $ Left $ backendError CouldNotVerifyPattern patternError
                Right pat -> do
                    let cutPoints = fromMaybe [] req.cutPointRules
                        terminals = fromMaybe [] req.terminalRules
                        mbDepth = fmap getNat req.maxDepth
                    execResponse <$> performRewrite def mLlvmLibrary mbDepth cutPoints terminals pat
        AddModule req -> do
            -- block other request executions while modifying the server state
            state <- liftIO $ takeMVar stateVar
            let abortWith err = do
                    liftIO (putMVar stateVar state)
                    pure $ Left err
                listNames :: (HasField "name" a b, HasField "getId" b Text) => [a] -> Text
                listNames = Text.intercalate ", " . map (.name.getId)

            case parseKoreModule "rpc-request" req._module of
                Left errMsg ->
                    abortWith $ backendError CouldNotParsePattern errMsg
                Right newModule ->
                    -- constraints on add-module imposed by LLVM simplification library:
                    let checkModule = do
                            unless (null newModule.sorts) $
                                throwE . AddModuleError $
                                    "Module introduces new sorts: " <> listNames newModule.sorts
                            unless (null $ newModule.symbols) $
                                throwE . AddModuleError $
                                    "Module introduces new symbols: " <> listNames newModule.symbols
                     in case runExcept (checkModule >> addToDefinitions newModule state.definitions) of
                            Left err ->
                                abortWith $ backendError CouldNotVerifyPattern err
                            Right newDefinitions -> do
                                liftIO $ putMVar stateVar state{definitions = newDefinitions}
                                Log.logInfo $ "Added a new module. Now in scope: " <> Text.intercalate ", " (Map.keys newDefinitions)
                                pure $ Right $ AddModule ()

        -- this case is only reachable if the cancel appeared as part of a batch request
        Cancel -> pure $ Left cancelUnsupportedInBatchMode
        -- using "Method does not exist" error code
        _ -> pure $ Left notImplemented
  where
    withContext ::
        Maybe Text ->
        ((KoreDefinition, Maybe LLVM.API) -> m (Either ErrorObj (API 'Res))) ->
        m (Either ErrorObj (API 'Res))
    withContext mbMainModule action = do
        state <- liftIO $ readMVar stateVar
        let mainName = fromMaybe state.defaultMain mbMainModule
        case Map.lookup mainName state.definitions of
            Nothing -> pure $ Left $ backendError CouldNotFindModule mainName
            Just d -> action (d, state.mLlvmLibrary)

    execResponse :: (Natural, RewriteResult Pattern) -> Either ErrorObj (API 'Res)
    execResponse (_, RewriteSingle{}) =
        error "Single rewrite result"
    execResponse (d, RewriteBranch p nexts) =
        Right $
            Execute
                ExecuteResult
                    { reason = Branching
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Just $ map toExecState $ toList nexts
                    , rule = Nothing
                    }
    execResponse (d, RewriteStuck p) =
        Right $
            Execute
                ExecuteResult
                    { reason = Stuck
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }
    execResponse (d, RewriteCutPoint lbl p next) =
        Right $
            Execute
                ExecuteResult
                    { reason = CutPointRule
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Just [toExecState next]
                    , rule = Just lbl
                    }
    execResponse (d, RewriteTerminal lbl p) =
        Right $
            Execute
                ExecuteResult
                    { reason = TerminalRule
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Just lbl
                    }
    execResponse (d, RewriteStopped p) =
        Right $
            Execute
                ExecuteResult
                    { reason = DepthBound
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }
    execResponse (d, RewriteAborted p) =
        Right $
            Execute
                ExecuteResult
                    { reason = Kore.JsonRpc.Types.Aborted
                    , depth = Depth d
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }

    toExecState :: Pattern -> ExecuteState
    toExecState pat =
        ExecuteState{term = addHeader t, predicate = fmap addHeader p, substitution = Nothing}
      where
        (t, p) = externalisePattern pat

runServer ::
    Int ->
    Map Text KoreDefinition ->
    Text ->
    Maybe LLVM.API ->
    (LogLevel, [LogLevel]) ->
    IO ()
runServer port definitions defaultMain mLlvmLibrary (logLevel, customLevels) =
    do
        stateVar <- newMVar ServerState{definitions, defaultMain, mLlvmLibrary}
        Log.runStderrLoggingT . Log.filterLogger levelFilter $
            jsonRpcServer
                srvSettings
                (const $ respond stateVar)
                [handleErrorCall, handleSomeException]
  where
    levelFilter _source lvl =
        lvl `elem` customLevels || lvl >= logLevel && lvl <= LevelError

    srvSettings = serverSettings port "*"

data ServerState = ServerState
    { definitions :: Map Text KoreDefinition
    -- ^ definitions for each loaded module as main module
    , defaultMain :: Text
    -- ^ default main module (initially from command line, could be changed later)
    , mLlvmLibrary :: Maybe LLVM.API
    -- ^ optional LLVM simplification library
    }
