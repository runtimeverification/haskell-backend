{- |
Module      : Booster.JsonRpc
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.JsonRpc (
    module Booster.JsonRpc,
    rpcJsonConfig,
) where

import Control.Monad.Logger.CallStack (LogLevel (LevelError), MonadLoggerIO)
import Control.Monad.Logger.CallStack qualified as Log
import Control.Monad.Trans.Except (runExcept)
import Data.Conduit.Network (serverSettings)
import Data.Foldable
import Data.Maybe (fromMaybe, isJust)
import Data.Text qualified as Text
import Numeric.Natural

import Booster.Definition.Base (KoreDefinition (..))
import Booster.LLVM.Internal qualified as LLVM
import Booster.Pattern.Base (Pattern)
import Booster.Pattern.Rewrite (RewriteResult (..), performRewrite)
import Booster.Syntax.Json (KoreJson (..), addHeader)
import Booster.Syntax.Json.Externalise (externalisePattern)
import Booster.Syntax.Json.Internalise (internalisePattern)
import Kore.JsonRpc.Error
import Kore.JsonRpc.Server
import Kore.JsonRpc.Types

respond ::
    forall m.
    MonadLoggerIO m =>
    KoreDefinition ->
    Maybe LLVM.API ->
    Respond (API 'Req) m (API 'Res)
respond def@KoreDefinition{} mLlvmLibrary =
    \case
        Execute req
            | isJust req._module -> pure $ Left $ unsupportedOption ("module" :: String)
            | isJust req.stepTimeout -> pure $ Left $ unsupportedOption ("step-timeout" :: String)
            | isJust req.movingAverageStepTimeout -> pure $ Left $ unsupportedOption ("moving-average-step-timeout" :: String)
        Execute req -> do
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

        -- this case is only reachable if the cancel appeared as part of a batch request
        Cancel -> pure $ Left cancelUnsupportedInBatchMode
        -- using "Method does not exist" error code

        _ -> pure $ Left notImplemented
  where
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

runServer :: Int -> KoreDefinition -> Maybe LLVM.API -> (LogLevel, [LogLevel]) -> IO ()
runServer port internalizedModule mLlvmLibrary (logLevel, customLevels) =
    do
        Log.runStderrLoggingT . Log.filterLogger levelFilter
        $ jsonRpcServer
            srvSettings
            (const $ respond internalizedModule mLlvmLibrary)
            [handleErrorCall, handleSomeException]
  where
    levelFilter _source lvl =
        lvl `elem` customLevels || lvl >= logLevel && lvl <= LevelError

    srvSettings = serverSettings port "*"
