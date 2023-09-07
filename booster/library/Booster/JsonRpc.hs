{-# LANGUAGE FlexibleContexts #-}

{- |
Module      : Booster.JsonRpc
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.JsonRpc (
    ServerState (..),
    respond,
    runServer,
    RpcTypes.rpcJsonConfig,
    execStateToKoreJson,
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
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import Data.Text (Text, pack)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import GHC.Records
import Numeric.Natural

import Booster.Definition.Attributes.Base (getUniqueId, uniqueId)
import Booster.Definition.Base (KoreDefinition (..))
import Booster.Definition.Base qualified as Definition (RewriteRule (..))
import Booster.LLVM.Internal qualified as LLVM
import Booster.Pattern.ApplyEquations qualified as ApplyEquations
import Booster.Pattern.Base (Pattern (..), TermOrPredicate (..))
import Booster.Pattern.Rewrite (
    RewriteFailed (..),
    RewriteResult (..),
    RewriteTrace (..),
    performRewrite,
 )
import Booster.Pattern.Util (sortOfPattern)
import Booster.Syntax.Json (KoreJson (..), addHeader, sortOfJson)
import Booster.Syntax.Json.Externalise
import Booster.Syntax.Json.Internalise (internalisePattern, internaliseTermOrPredicate)
import Booster.Syntax.ParsedKore (parseKoreModule)
import Booster.Syntax.ParsedKore.Base
import Booster.Syntax.ParsedKore.Internalise (DefinitionError (..), addToDefinitions)
import Data.List (singleton)
import Data.Sequence (Seq)
import Kore.JsonRpc.Error qualified as RpcError
import Kore.JsonRpc.Server
import Kore.JsonRpc.Types qualified as RpcTypes
import Kore.JsonRpc.Types.Log
import Kore.Syntax.Json.Types (Id (..))
import Kore.Syntax.Json.Types qualified as KoreJson

respond ::
    forall m.
    MonadLoggerIO m =>
    MVar ServerState ->
    Respond (RpcTypes.API 'RpcTypes.Req) m (RpcTypes.API 'RpcTypes.Res)
respond stateVar =
    \case
        RpcTypes.Execute req
            | isJust req.stepTimeout -> pure $ Left $ RpcError.unsupportedOption ("step-timeout" :: String)
            | isJust req.movingAverageStepTimeout ->
                pure $ Left $ RpcError.unsupportedOption ("moving-average-step-timeout" :: String)
        RpcTypes.Execute req -> withContext req._module $ \(def, mLlvmLibrary) -> do
            -- internalise given constrained term
            let internalised = runExcept $ internalisePattern False Nothing def req.state.term

            case internalised of
                Left patternError -> do
                    Log.logDebug $ "Error internalising cterm" <> Text.pack (show patternError)
                    pure $ Left $ RpcError.backendError RpcError.CouldNotVerifyPattern patternError
                Right pat -> do
                    let cutPoints = fromMaybe [] req.cutPointRules
                        terminals = fromMaybe [] req.terminalRules
                        mbDepth = fmap RpcTypes.getNat req.maxDepth
                        doTracing =
                            any
                                (fromMaybe False)
                                [ req.logSuccessfulRewrites
                                , req.logFailedRewrites
                                , req.logSuccessfulSimplifications
                                , req.logFailedSimplifications
                                ]
                    execResponse req <$> performRewrite doTracing def mLlvmLibrary mbDepth cutPoints terminals pat
        RpcTypes.AddModule req -> do
            -- block other request executions while modifying the server state
            state <- liftIO $ takeMVar stateVar
            let abortWith err = do
                    liftIO (putMVar stateVar state)
                    pure $ Left err
                listNames :: (HasField "name" a b, HasField "getId" b Text) => [a] -> Text
                listNames = Text.intercalate ", " . map (.name.getId)

            case parseKoreModule "rpc-request" req._module of
                Left errMsg ->
                    abortWith $ RpcError.backendError RpcError.CouldNotParsePattern errMsg
                Right newModule ->
                    -- constraints on add-module imposed by LLVM simplification library:
                    let checkModule = do
                            unless (null newModule.sorts) $
                                throwE . AddModuleError $
                                    "Module introduces new sorts: " <> listNames newModule.sorts
                            unless (null newModule.symbols) $
                                throwE . AddModuleError $
                                    "Module introduces new symbols: " <> listNames newModule.symbols
                     in case runExcept (checkModule >> addToDefinitions newModule state.definitions) of
                            Left err ->
                                abortWith $ RpcError.backendError RpcError.CouldNotVerifyPattern err
                            Right newDefinitions -> do
                                liftIO $ putMVar stateVar state{definitions = newDefinitions}
                                Log.logInfo $
                                    "Added a new module. Now in scope: " <> Text.intercalate ", " (Map.keys newDefinitions)
                                pure $ Right $ RpcTypes.AddModule ()
        RpcTypes.Simplify req -> withContext req._module $ \(def, mLlvmLibrary) -> do
            let internalised =
                    runExcept $ internaliseTermOrPredicate False Nothing def req.state.term
            let mkTraces
                    | all not . catMaybes $
                        [req.logSuccessfulSimplifications, req.logFailedSimplifications] =
                        const Nothing
                    | otherwise =
                        Just
                            . mapMaybe (mkLogEquationTrace (req.logSuccessfulSimplifications, req.logFailedSimplifications))
                            . toList
                doTracing =
                    any
                        (fromMaybe False)
                        [ req.logSuccessfulSimplifications
                        , req.logFailedSimplifications
                        ]
            case internalised of
                Left patternErrors -> do
                    Log.logError $ "Error internalising cterm: " <> Text.pack (show patternErrors)
                    pure $ Left $ RpcError.backendError RpcError.CouldNotVerifyPattern patternErrors
                -- term and predicate (pattern)
                Right (TermAndPredicate pat) -> do
                    Log.logInfoNS "booster" "Simplifying a pattern"
                    ApplyEquations.evaluatePattern doTracing def mLlvmLibrary pat >>= \case
                        (Right newPattern, patternTraces) -> do
                            let (term, mbPredicate, mbSubstitution) = externalisePattern newPattern
                                tSort = externaliseSort (sortOfPattern newPattern)
                                predicate = fromMaybe (KoreJson.KJTop tSort) mbPredicate
                                substitution = fromMaybe (KoreJson.KJTop tSort) mbSubstitution
                                result = KoreJson.KJAnd tSort (KoreJson.KJAnd tSort term predicate) substitution
                            pure . Right . RpcTypes.Simplify $
                                RpcTypes.SimplifyResult
                                    { state = addHeader result
                                    , logs = mkTraces patternTraces
                                    }
                        (Left ApplyEquations.SideConditionsFalse{}, patternTraces) -> do
                            let tSort = fromMaybe (error "unknown sort") $ sortOfJson req.state.term
                            pure . Right . RpcTypes.Simplify $
                                RpcTypes.SimplifyResult
                                    { state = addHeader $ KoreJson.KJBottom tSort
                                    , logs = mkTraces patternTraces
                                    }
                        (Left (ApplyEquations.EquationLoop terms), _traces) ->
                            pure . Left . RpcError.backendError RpcError.Aborted $ map externaliseTerm terms -- FIXME
                        (Left other, _traces) ->
                            pure . Left . RpcError.backendError RpcError.Aborted $ show other -- FIXME
                            -- predicate only
                Right (APredicate predicate) -> do
                    Log.logInfoNS "booster" "Simplifying a predicate"
                    ApplyEquations.simplifyConstraint doTracing def mLlvmLibrary predicate >>= \case
                        (Right newPred, traces) -> do
                            let predicateSort =
                                    fromMaybe (error "not a predicate") $
                                        sortOfJson req.state.term
                                result = externalisePredicate predicateSort newPred
                            pure . Right . RpcTypes.Simplify $
                                RpcTypes.SimplifyResult
                                    { state = addHeader result
                                    , logs = mkTraces traces
                                    }
                        (Left something, _traces) ->
                            pure . Left . RpcError.backendError RpcError.Aborted $ show something -- FIXME

        -- this case is only reachable if the cancel appeared as part of a batch request
        RpcTypes.Cancel -> pure $ Left RpcError.cancelUnsupportedInBatchMode
        -- using "Method does not exist" error code
        _ -> pure $ Left RpcError.notImplemented
  where
    withContext ::
        Maybe Text ->
        ((KoreDefinition, Maybe LLVM.API) -> m (Either ErrorObj (RpcTypes.API 'RpcTypes.Res))) ->
        m (Either ErrorObj (RpcTypes.API 'RpcTypes.Res))
    withContext mbMainModule action = do
        state <- liftIO $ readMVar stateVar
        let mainName = fromMaybe state.defaultMain mbMainModule
        case Map.lookup mainName state.definitions of
            Nothing -> pure $ Left $ RpcError.backendError RpcError.CouldNotFindModule mainName
            Just d -> action (d, state.mLlvmLibrary)

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
                [RpcError.handleErrorCall, RpcError.handleSomeException]
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

execStateToKoreJson :: RpcTypes.ExecuteState -> KoreJson.KoreJson
execStateToKoreJson RpcTypes.ExecuteState{term = t, substitution, predicate} =
    let subAndPred = catMaybes [KoreJson.term <$> substitution, KoreJson.term <$> predicate]
        innerSorts = mapMaybe sortOfJson $ KoreJson.term t : subAndPred
        topLevelSort = case innerSorts of
            [] -> KoreJson.SortApp (KoreJson.Id "SortGeneratedTopCell") []
            xs ->
                if all (== head xs) (tail xs) -- we know xs is non-empty, hence `head` is safe here
                    then KoreJson.SortApp (head xs).name []
                    else KoreJson.SortApp (KoreJson.Id "SortGeneratedTopCell") []
     in t
            { KoreJson.term =
                foldr (KoreJson.KJAnd topLevelSort) t.term subAndPred
            }

execResponse ::
    RpcTypes.ExecuteRequest ->
    (Natural, Seq (RewriteTrace Pattern), RewriteResult Pattern) ->
    Either ErrorObj (RpcTypes.API 'RpcTypes.Res)
execResponse req (d, traces, rr) = case rr of
    RewriteBranch p nexts ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.Branching
                    , depth
                    , logs
                    , state = toExecState p
                    , nextStates = Just $ map (\(_, _, p') -> toExecState p') $ toList nexts
                    , rule = Nothing
                    }
    RewriteStuck p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.Stuck
                    , depth
                    , logs
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }
    RewriteTrivial p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.Vacuous
                    , depth
                    , logs
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }
    RewriteCutPoint lbl _ p next ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.CutPointRule
                    , depth
                    , logs
                    , state = toExecState p
                    , nextStates = Just [toExecState next]
                    , rule = Just lbl
                    }
    RewriteTerminal lbl _ p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.TerminalRule
                    , depth
                    , logs
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Just lbl
                    }
    RewriteFinished _ _ p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.DepthBound
                    , depth
                    , logs
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }
    RewriteAborted p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.Aborted
                    , depth
                    , logs
                    , state = toExecState p
                    , nextStates = Nothing
                    , rule = Nothing
                    }
  where
    RpcTypes.ExecuteRequest
        { logSuccessfulRewrites
        , logFailedRewrites
        , logSuccessfulSimplifications
        , logFailedSimplifications
        } = req
    depth = RpcTypes.Depth d

    logs
        | not
            ( fromMaybe False logSuccessfulRewrites
                || fromMaybe False logFailedRewrites
                || fromMaybe False logSuccessfulSimplifications
                || fromMaybe False logFailedSimplifications
            ) =
            Nothing
        | otherwise =
            fmap concat
                . mapM
                    ( mkLogRewriteTrace
                        (logSuccessfulRewrites, logFailedRewrites)
                        (logSuccessfulSimplifications, logFailedSimplifications)
                    )
                $ toList traces

toExecState :: Pattern -> RpcTypes.ExecuteState
toExecState pat =
    RpcTypes.ExecuteState
        { term = addHeader t
        , predicate = fmap addHeader p
        , substitution = fmap addHeader s
        }
  where
    (t, p, s) = externalisePattern pat

mkLogEquationTrace :: (Maybe Bool, Maybe Bool) -> ApplyEquations.EquationTrace -> Maybe LogEntry
mkLogEquationTrace
    (logSuccessfulSimplifications, logFailedSimplifications)
    ApplyEquations.EquationTrace{subjectTerm, ruleId = uid, result} =
        case result of
            ApplyEquations.Success rewrittenTrm
                | fromMaybe False logSuccessfulSimplifications ->
                    Just $
                        Simplification
                            { originalTerm
                            , originalTermIndex
                            , origin
                            , result =
                                Success
                                    { rewrittenTerm = Just $ execStateToKoreJson $ toExecState $ Pattern rewrittenTrm []
                                    , substitution = Nothing
                                    , ruleId = fromMaybe "UNKNOWN" _ruleId
                                    }
                            }
            ApplyEquations.FailedMatch _failReason
                | fromMaybe False logFailedSimplifications ->
                    Just $
                        Simplification
                            { originalTerm
                            , originalTermIndex
                            , origin
                            , result = Failure{reason = "Failed match", _ruleId}
                            }
            ApplyEquations.IndeterminateMatch
                | fromMaybe False logFailedSimplifications ->
                    Just $
                        Simplification
                            { originalTerm
                            , originalTermIndex
                            , origin
                            , result = Failure{reason = "Indeterminate match", _ruleId}
                            }
            ApplyEquations.IndeterminateCondition _failedConditions
                | fromMaybe False logFailedSimplifications ->
                    Just $
                        Simplification
                            { originalTerm
                            , originalTermIndex
                            , origin
                            , result = Failure{reason = "Indeterminate side-condition", _ruleId}
                            }
            ApplyEquations.ConditionFalse
                | fromMaybe False logFailedSimplifications ->
                    Just $
                        Simplification
                            { originalTerm
                            , originalTermIndex
                            , origin
                            , result = Failure{reason = "Side-condition is false", _ruleId}
                            }
            ApplyEquations.RuleNotPreservingDefinedness
                | fromMaybe False logFailedSimplifications ->
                    Just $
                        Simplification
                            { originalTerm
                            , originalTermIndex
                            , origin
                            , result = Failure{reason = "The equation does not preserve definedness", _ruleId}
                            }
            ApplyEquations.MatchConstraintViolated _ varName
                | fromMaybe False logFailedSimplifications ->
                    Just $
                        Simplification
                            { originalTerm
                            , originalTermIndex
                            , origin
                            , result =
                                Failure
                                    { reason = "Symbolic/concrete constraint violated for variable: " <> Text.decodeUtf8 varName
                                    , _ruleId
                                    }
                            }
            _ -> Nothing
      where
        originalTerm = Just $ execStateToKoreJson $ toExecState $ Pattern subjectTerm []
        originalTermIndex = Nothing
        origin = Booster
        _ruleId = fmap getUniqueId uid

mkLogRewriteTrace ::
    (Maybe Bool, Maybe Bool) ->
    (Maybe Bool, Maybe Bool) ->
    RewriteTrace Pattern ->
    Maybe [LogEntry]
mkLogRewriteTrace
    (logSuccessfulRewrites, logFailedRewrites)
    equationLogOpts@(logSuccessfulSimplifications, logFailedSimplifications) =
        \case
            RewriteSingleStep _ uid _ res
                | fromMaybe False logSuccessfulRewrites ->
                    Just $
                        singleton $
                            Rewrite
                                { result =
                                    Success
                                        { rewrittenTerm = Just $ execStateToKoreJson $ toExecState res
                                        , substitution = Nothing
                                        , ruleId = maybe "UNKNOWN" getUniqueId uid
                                        }
                                , origin = Booster
                                }
            RewriteBranchingStep _ _ -> Nothing -- we may or may not want to emit a trace here in the future
            RewriteStepFailed reason
                | fromMaybe False logFailedRewrites ->
                    Just $
                        singleton $
                            Rewrite
                                { result = case reason of
                                    NoRulesForTerm{} -> Failure{reason = "No rules found", _ruleId = Nothing}
                                    NoApplicableRules{} -> Failure{reason = "No applicable rules found", _ruleId = Nothing}
                                    TermIndexIsNone{} -> Failure{reason = "Term index is None for term", _ruleId = Nothing}
                                    RuleApplicationUnclear r _ _ ->
                                        Failure
                                            { reason = "Uncertain about unification of rule"
                                            , _ruleId = fmap getUniqueId (uniqueId $ Definition.attributes r)
                                            }
                                    RuleConditionUnclear r _ ->
                                        Failure
                                            { reason = "Uncertain about a condition in rule"
                                            , _ruleId = fmap getUniqueId (uniqueId $ Definition.attributes r)
                                            }
                                    DefinednessUnclear r _ undefReasons ->
                                        Failure
                                            { reason = "Uncertain about definedness of rule because of: " <> pack (show undefReasons)
                                            , _ruleId = fmap getUniqueId (uniqueId $ Definition.attributes r)
                                            }
                                    UnificationIsNotMatch r _ _ ->
                                        Failure
                                            { reason = "Unification produced a non-match"
                                            , _ruleId = fmap getUniqueId (uniqueId $ Definition.attributes r)
                                            }
                                    RewriteSortError r _ _ ->
                                        Failure
                                            { reason = "Sort error while unifying"
                                            , _ruleId = fmap getUniqueId (uniqueId $ Definition.attributes r)
                                            }
                                , origin = Booster
                                }
            RewriteSimplified equationTraces Nothing
                | fromMaybe False logSuccessfulSimplifications || fromMaybe False logFailedSimplifications ->
                    mapM (mkLogEquationTrace equationLogOpts) equationTraces
            RewriteSimplified equationTraces (Just failure)
                | fromMaybe False logFailedSimplifications -> do
                    let final = singleton $ case failure of
                            ApplyEquations.IndexIsNone trm ->
                                Simplification
                                    { originalTerm = Just $ execStateToKoreJson $ toExecState $ Pattern trm []
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result = Failure{reason = "No index found for term", _ruleId = Nothing}
                                    }
                            ApplyEquations.TooManyIterations i _ _ ->
                                Simplification
                                    { originalTerm = Nothing
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result = Failure{reason = "Reached iteration depth limit " <> pack (show i), _ruleId = Nothing}
                                    }
                            ApplyEquations.EquationLoop _ ->
                                Simplification
                                    { originalTerm = Nothing
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result = Failure{reason = "Loop detected", _ruleId = Nothing}
                                    }
                            ApplyEquations.InternalError err ->
                                Simplification
                                    { originalTerm = Nothing
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result = Failure{reason = "Internal error: " <> err, _ruleId = Nothing}
                                    }
                            ApplyEquations.SideConditionsFalse _predicates ->
                                Simplification
                                    { originalTerm = Nothing
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result = Failure{reason = "Side conditions false", _ruleId = Nothing}
                                    }
                    (<> final) <$> mapM (mkLogEquationTrace equationLogOpts) equationTraces
            _ -> Nothing
