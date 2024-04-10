{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

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
    toExecState,
) where

import Control.Applicative ((<|>))
import Control.Concurrent (MVar, newMVar, putMVar, readMVar, takeMVar)
import Control.Monad
import Control.Monad.Extra (whenJust)
import Control.Monad.IO.Class
import Control.Monad.Logger.CallStack (LogLevel (LevelError), MonadLoggerIO)
import Control.Monad.Logger.CallStack qualified as Log
import Control.Monad.Trans.Except (catchE, except, runExcept, runExceptT, throwE, withExceptT)
import Crypto.Hash (SHA256 (..), hashWith)
import Data.Bifunctor (second)
import Data.Coerce (coerce)
import Data.Conduit.Network (serverSettings)
import Data.Foldable
import Data.List (singleton)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import Data.Sequence (Seq)
import Data.Text (Text, pack)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import GHC.Records
import Numeric.Natural
import Prettyprinter (pretty)
import System.Clock (Clock (Monotonic), diffTimeSpec, getTime, toNanoSecs)

import Booster.Definition.Attributes.Base (getUniqueId, uniqueId)
import Booster.Definition.Base (KoreDefinition (..))
import Booster.Definition.Base qualified as Definition (RewriteRule (..))
import Booster.LLVM as LLVM (API)
import Booster.Pattern.ApplyEquations qualified as ApplyEquations
import Booster.Pattern.Base (
    Pattern (..),
    Term,
    Variable,
 )
import Booster.Pattern.Base qualified as Pattern
import Booster.Pattern.Rewrite (
    RewriteFailed (..),
    RewriteResult (..),
    RewriteTrace (..),
    performRewrite,
 )
import Booster.Pattern.Util (sortOfPattern, substituteInPredicate, substituteInTerm)
import Booster.Prettyprinter (renderText)
import Booster.SMT.Base qualified as SMT
import Booster.SMT.Interface qualified as SMT
import Booster.Syntax.Json (KoreJson (..), addHeader, prettyPattern, sortOfJson)
import Booster.Syntax.Json.Externalise
import Booster.Syntax.Json.Internalise (
    InternalisedPredicates (..),
    TermOrPredicates (..),
    internalisePattern,
    internaliseTermOrPredicate,
    pattern CheckSubsorts,
    pattern DisallowAlias,
 )
import Booster.Syntax.ParsedKore (parseKoreModule)
import Booster.Syntax.ParsedKore.Base hiding (ParsedModule)
import Booster.Syntax.ParsedKore.Base qualified as ParsedModule (ParsedModule (..))
import Booster.Syntax.ParsedKore.Internalise (addToDefinitions)
import Booster.Util (Flag (..), constructorName)
import Data.Aeson (ToJSON (toJSON))
import Data.Set qualified as Set
import Kore.JsonRpc.Error qualified as RpcError
import Kore.JsonRpc.Server
import Kore.JsonRpc.Types qualified as RpcTypes
import Kore.JsonRpc.Types.Log
import Kore.Syntax.Json.Types (Id (..))
import Kore.Syntax.Json.Types qualified as KoreJson
import Kore.Syntax.Json.Types qualified as Syntax

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
        RpcTypes.Execute req -> withContext req._module $ \(def, mLlvmLibrary, mSMTOptions) -> do
            start <- liftIO $ getTime Monotonic
            -- internalise given constrained term
            let internalised = runExcept $ internalisePattern DisallowAlias CheckSubsorts Nothing def req.state.term

            case internalised of
                Left patternError -> do
                    Log.logDebug $ "Error internalising cterm" <> Text.pack (show patternError)
                    pure $ Left $ RpcError.backendError RpcError.CouldNotVerifyPattern patternError
                Right (pat, substitution, unsupported) -> do
                    unless (null unsupported) $ do
                        Log.logWarnNS
                            "booster"
                            "Execute: ignoring unsupported predicate parts"
                        Log.logOtherNS
                            "booster"
                            (Log.LevelOther "ErrorDetails")
                            (Text.unlines $ map prettyPattern unsupported)
                    let cutPoints = fromMaybe [] req.cutPointRules
                        terminals = fromMaybe [] req.terminalRules
                        mbDepth = fmap RpcTypes.getNat req.maxDepth
                        doTracing =
                            Flag $
                                any
                                    (fromMaybe False)
                                    [ req.logSuccessfulRewrites
                                    , req.logFailedRewrites
                                    , req.logSuccessfulSimplifications
                                    , req.logFailedSimplifications
                                    , req.logFallbacks
                                    ]
                    -- apply the given substitution before doing anything else
                    let substPat =
                            Pattern
                                { term = substituteInTerm substitution pat.term
                                , constraints = Set.map (substituteInPredicate substitution) pat.constraints
                                , ceilConditions = pat.ceilConditions
                                }

                    solver <- traverse (SMT.initSolver def) mSMTOptions
                    result <-
                        performRewrite doTracing def mLlvmLibrary solver mbDepth cutPoints terminals substPat
                    whenJust solver SMT.closeSolver
                    stop <- liftIO $ getTime Monotonic
                    let duration =
                            if fromMaybe False req.logTiming
                                then
                                    Just $
                                        fromIntegral (toNanoSecs (diffTimeSpec stop start)) / 1e9
                                else Nothing
                    pure $ execResponse duration req result substitution unsupported
        RpcTypes.AddModule RpcTypes.AddModuleRequest{_module, nameAsId = nameAsId'} -> runExceptT $ do
            -- block other request executions while modifying the server state
            state <- liftIO $ takeMVar stateVar
            let nameAsId = fromMaybe False nameAsId'
                moduleHash = Text.pack $ ('m' :) . show . hashWith SHA256 $ Text.encodeUtf8 _module
                restoreStateAndRethrow (errTy, errMsg) = do
                    liftIO (putMVar stateVar state)
                    throwE $ RpcError.backendError errTy errMsg
                listNames :: (HasField "name" a b, HasField "getId" b Text) => [a] -> Text
                listNames = Text.intercalate ", " . map (.name.getId)

            flip catchE restoreStateAndRethrow $ do
                newModule <-
                    withExceptT ((RpcError.InvalidModule,) . toJSON) $
                        except $
                            parseKoreModule "rpc-request" _module

                unless (null newModule.sorts) $
                    throwE
                        ( RpcError.InvalidModule
                        , toJSON $
                            "Module introduces new sorts: " <> listNames newModule.sorts
                        )
                unless (null newModule.symbols) $
                    throwE
                        ( RpcError.InvalidModule
                        , toJSON $
                            "Module introduces new symbols: " <> listNames newModule.symbols
                        )

                when nameAsId $
                    case (Map.lookup (getId $ newModule.name) state.definitions, Map.lookup moduleHash state.definitions) of
                        (Just{}, Nothing) ->
                            -- another module with the same name already exists
                            throwE (RpcError.DuplicateModuleName, toJSON $ getId $ newModule.name)
                        (Just nmMod, Just idMod)
                            | nmMod /= idMod ->
                                -- this module has previously been added and different
                                -- module with the same name also already exists
                                throwE (RpcError.DuplicateModuleName, toJSON $ getId $ newModule.name)
                            | otherwise ->
                                -- this module has previously been added with name-as-id: true
                                -- we can allow this, since the contents of the named module
                                -- are the same
                                pure ()
                        _ -> pure ()

                newDefinitions <-
                    withExceptT ((RpcError.InvalidModule,) . toJSON) $
                        except $
                            runExcept $
                                addToDefinitions newModule{ParsedModule.name = Id moduleHash} state.definitions

                liftIO $
                    putMVar
                        stateVar
                        state
                            { definitions =
                                if nameAsId
                                    then Map.insert (getId $ newModule.name) (newDefinitions Map.! moduleHash) newDefinitions
                                    else newDefinitions
                            }
                Log.logInfo $
                    "Added a new module. Now in scope: " <> Text.intercalate ", " (Map.keys newDefinitions)
                pure $ RpcTypes.AddModule $ RpcTypes.AddModuleResult moduleHash
        RpcTypes.Simplify req -> withContext req._module $ \(def, mLlvmLibrary, mSMTOptions) -> do
            start <- liftIO $ getTime Monotonic
            let internalised =
                    runExcept $ internaliseTermOrPredicate DisallowAlias CheckSubsorts Nothing def req.state.term
            let mkEquationTraces
                    | coerce doTracing =
                        Just
                            . mapMaybe
                                ( mkLogEquationTrace
                                    ( fromMaybe False req.logSuccessfulSimplifications
                                    , fromMaybe False req.logFailedSimplifications
                                    )
                                )
                    | otherwise =
                        const Nothing
                mkTraces duration traceData
                    | Just True <- req.logTiming =
                        Just $
                            [ProcessingTime (Just Booster) duration]
                                <> fromMaybe [] (mkEquationTraces traceData)
                    | otherwise =
                        mkEquationTraces traceData
                doTracing =
                    Flag $
                        any
                            (fromMaybe False)
                            [ req.logSuccessfulSimplifications
                            , req.logFailedSimplifications
                            ]

            solver <- traverse (SMT.initSolver def) mSMTOptions

            result <- case internalised of
                Left patternErrors -> do
                    Log.logErrorNS "booster" $
                        "Error internalising cterm: " <> Text.pack (show patternErrors)
                    Log.logOtherNS
                        "booster"
                        (Log.LevelOther "ErrorDetails")
                        (prettyPattern req.state.term)
                    pure $ Left $ RpcError.backendError RpcError.CouldNotVerifyPattern patternErrors
                -- term and predicate (pattern)
                Right (TermAndPredicates pat substitution unsupported) -> do
                    Log.logInfoNS "booster" "Simplifying a pattern"
                    unless (null unsupported) $ do
                        Log.logWarnNS
                            "booster"
                            "Simplify: ignoring unsupported predicates in input"
                        Log.logOtherNS
                            "booster"
                            (Log.LevelOther "ErrorDetails")
                            (Text.unlines $ map prettyPattern unsupported)
                    -- apply the given substitution before doing anything else
                    let substPat =
                            Pattern
                                { term = substituteInTerm substitution pat.term
                                , constraints = Set.map (substituteInPredicate substitution) pat.constraints
                                , ceilConditions = pat.ceilConditions
                                }
                    ApplyEquations.evaluatePattern doTracing def mLlvmLibrary solver mempty substPat >>= \case
                        (Right newPattern, patternTraces, _) -> do
                            let (term, mbPredicate, mbSubstitution) = externalisePattern newPattern substitution
                                tSort = externaliseSort (sortOfPattern newPattern)
                                result = case catMaybes (mbPredicate : mbSubstitution : map Just unsupported) of
                                    [] -> term
                                    ps -> KoreJson.KJAnd tSort $ term : ps
                            pure $ Right (addHeader result, patternTraces)
                        (Left ApplyEquations.SideConditionFalse{}, patternTraces, _) -> do
                            let tSort = externaliseSort $ sortOfPattern pat
                            pure $ Right (addHeader $ KoreJson.KJBottom tSort, patternTraces)
                        (Left (ApplyEquations.EquationLoop terms), _traces, _) ->
                            pure . Left . RpcError.backendError RpcError.Aborted $ map externaliseTerm terms -- FIXME
                        (Left other, _traces, _) ->
                            pure . Left . RpcError.backendError RpcError.Aborted $ (Text.pack . constructorName $ other) -- FIXME
                            -- predicate only
                Right (Predicates ps)
                    | null ps.boolPredicates && null ps.ceilPredicates && null ps.substitution && null ps.unsupported ->
                        pure $
                            Right
                                (addHeader $ Syntax.KJTop (fromMaybe (error "not a predicate") $ sortOfJson req.state.term), [])
                    | otherwise -> do
                        Log.logInfoNS "booster" "Simplifying predicates"
                        unless (null ps.unsupported) $ do
                            Log.logWarnNS
                                "booster"
                                "Simplify: ignoring unsupported predicates in input"
                            Log.logOtherNS
                                "booster"
                                (Log.LevelOther "ErrorDetails")
                                (Text.unlines $ map prettyPattern ps.unsupported)
                        Log.logOtherNS "booster" (Log.LevelOther "Simplify") $ renderText (pretty ps)
                        let predicates = map (substituteInPredicate ps.substitution) $ Set.toList ps.boolPredicates
                        ApplyEquations.simplifyConstraints
                            doTracing
                            def
                            mLlvmLibrary
                            solver
                            mempty
                            predicates
                            >>= \case
                                (Right newPreds, traces, _) -> do
                                    let predicateSort =
                                            fromMaybe (error "not a predicate") $
                                                sortOfJson req.state.term
                                        result =
                                            map (externalisePredicate predicateSort) newPreds
                                                <> map (externaliseCeil predicateSort) (Set.toList ps.ceilPredicates)
                                                <> map (uncurry $ externaliseSubstitution predicateSort) (Map.toList ps.substitution)
                                                <> ps.unsupported

                                    pure $ Right (addHeader $ Syntax.KJAnd predicateSort result, traces)
                                (Left something, _traces, _) ->
                                    pure . Left . RpcError.backendError RpcError.Aborted $ show something
            whenJust solver SMT.closeSolver
            stop <- liftIO $ getTime Monotonic

            let duration =
                    fromIntegral (toNanoSecs (diffTimeSpec stop start)) / 1e9
                mkSimplifyResponse state traceData =
                    RpcTypes.Simplify
                        RpcTypes.SimplifyResult{state, logs = mkTraces duration traceData}
            pure $ second (uncurry mkSimplifyResponse) (fmap (second (map ApplyEquations.eraseStates)) result)
        RpcTypes.GetModel req -> withContext req._module $ \case
            (_, _, Nothing) -> do
                Log.logErrorNS "booster" "get-model request, not supported without SMT solver"
                pure $ Left RpcError.notImplemented
            (def, _, Just smtOptions) -> do
                let internalised =
                        runExcept $
                            internaliseTermOrPredicate DisallowAlias CheckSubsorts Nothing def req.state.term
                case internalised of
                    Left patternErrors -> do
                        Log.logErrorNS "booster" $
                            "Error internalising cterm: " <> Text.pack (show patternErrors)
                        Log.logOtherNS
                            "booster"
                            (Log.LevelOther "ErrorDetails")
                            (prettyPattern req.state.term)
                        pure $ Left $ RpcError.backendError RpcError.CouldNotVerifyPattern patternErrors
                    -- various predicates obtained
                    Right things -> do
                        Log.logInfoNS "booster" "get-model request"
                        -- term and predicates were sent. Only work on predicates
                        (boolPs, suppliedSubst) <-
                            case things of
                                TermAndPredicates pat substitution unsupported -> do
                                    Log.logWarnNS
                                        "booster"
                                        "get-model ignores supplied terms and only checks predicates"
                                    Log.logOtherNS
                                        "booster"
                                        (Log.LevelOther "ErrorDetails")
                                        (renderText $ pretty pat.term)
                                    unless (null unsupported) $ do
                                        Log.logWarnNS
                                            "booster"
                                            " get-model: ignoring unsupported predicates"
                                        Log.logOtherNS
                                            "booster"
                                            (Log.LevelOther "ErrorDetails")
                                            (Text.unlines $ map prettyPattern unsupported)
                                    pure (Set.toList pat.constraints, substitution)
                                Predicates ps -> do
                                    unless (null ps.ceilPredicates && null ps.unsupported) $ do
                                        Log.logWarnNS
                                            "booster"
                                            "get-model: ignoring supplied ceils and unsupported predicates"
                                        Log.logOtherNS
                                            "booster"
                                            (Log.LevelOther "ErrorDetails")
                                            ( Text.unlines $
                                                map
                                                    (renderText . ("#Ceil:" <>) . pretty)
                                                    (Set.toList ps.ceilPredicates)
                                                    <> map prettyPattern ps.unsupported
                                            )
                                    pure (Set.toList ps.boolPredicates, ps.substitution)

                        smtResult <-
                            if null boolPs && Map.null suppliedSubst
                                then do
                                    -- as per spec, no predicate, no answer
                                    Log.logOtherNS
                                        "booster"
                                        (Log.LevelOther "SMT")
                                        "No predicates or substitutions given, returning Unknown"
                                    pure $ Left SMT.Unknown
                                else do
                                    solver <-
                                        SMT.initSolver def smtOptions
                                    smtResult <-
                                        SMT.getModelFor solver boolPs suppliedSubst
                                    SMT.closeSolver solver
                                    pure smtResult
                        Log.logOtherNS "booster" (Log.LevelOther "SMT") $
                            "SMT result: " <> pack (either show (("Subst: " <>) . show . Map.size) smtResult)
                        pure . Right . RpcTypes.GetModel $ case smtResult of
                            Left SMT.Unsat ->
                                RpcTypes.GetModelResult
                                    { satisfiable = RpcTypes.Unsat
                                    , substitution = Nothing
                                    }
                            Left SMT.Unknown ->
                                RpcTypes.GetModelResult
                                    { satisfiable = RpcTypes.Unknown
                                    , substitution = Nothing
                                    }
                            Left other ->
                                error $ "Unexpected result " <> show other <> "from getModelFor"
                            Right subst ->
                                let sort = fromMaybe (error "Unknown sort in input") $ sortOfJson req.state.term
                                    substitution
                                        | Map.null subst = Nothing
                                        | [(var, term)] <- Map.assocs subst =
                                            Just . addHeader $
                                                KoreJson.KJEquals
                                                    (externaliseSort var.variableSort)
                                                    sort
                                                    (externaliseTerm $ Pattern.Var var)
                                                    (externaliseTerm term)
                                        | otherwise =
                                            Just . addHeader $
                                                KoreJson.KJAnd
                                                    sort
                                                    [ KoreJson.KJEquals
                                                        (externaliseSort var.variableSort)
                                                        sort
                                                        (externaliseTerm $ Pattern.Var var)
                                                        (externaliseTerm term)
                                                    | (var, term) <- Map.assocs subst
                                                    ]
                                 in RpcTypes.GetModelResult
                                        { satisfiable = RpcTypes.Sat
                                        , substitution
                                        }

        -- this case is only reachable if the cancel appeared as part of a batch request
        RpcTypes.Cancel -> pure $ Left RpcError.cancelUnsupportedInBatchMode
        -- using "Method does not exist" error code
        _ -> pure $ Left RpcError.notImplemented
  where
    withContext ::
        Maybe Text ->
        ( (KoreDefinition, Maybe LLVM.API, Maybe SMT.SMTOptions) ->
          m (Either ErrorObj (RpcTypes.API 'RpcTypes.Res))
        ) ->
        m (Either ErrorObj (RpcTypes.API 'RpcTypes.Res))
    withContext mbMainModule action = do
        state <- liftIO $ readMVar stateVar
        let mainName = fromMaybe state.defaultMain mbMainModule
        case Map.lookup mainName state.definitions of
            Nothing -> pure $ Left $ RpcError.backendError RpcError.CouldNotFindModule mainName
            Just d -> action (d, state.mLlvmLibrary, state.mSMTOptions)

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
        stateVar <- newMVar ServerState{definitions, defaultMain, mLlvmLibrary, mSMTOptions}
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
    , mSMTOptions :: Maybe SMT.SMTOptions
    -- ^ (optional) SMT solver options
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
                if null subAndPred then t.term else KoreJson.KJAnd topLevelSort (t.term : subAndPred)
            }

execResponse ::
    Maybe Double ->
    RpcTypes.ExecuteRequest ->
    (Natural, Seq (RewriteTrace ()), RewriteResult Pattern) ->
    Map Variable Term ->
    [Syntax.KorePattern] ->
    Either ErrorObj (RpcTypes.API 'RpcTypes.Res)
execResponse mbDuration req (d, traces, rr) originalSubstitution unsupported = case rr of
    RewriteBranch p nexts ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.Branching
                    , depth
                    , logs
                    , state = toExecState p originalSubstitution unsupported
                    , nextStates =
                        Just $ map (\(_, _, p') -> toExecState p' originalSubstitution unsupported) $ toList nexts
                    , rule = Nothing
                    , unknownPredicate = Nothing
                    }
    RewriteStuck p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.Stuck
                    , depth
                    , logs
                    , state = toExecState p originalSubstitution unsupported
                    , nextStates = Nothing
                    , rule = Nothing
                    , unknownPredicate = Nothing
                    }
    RewriteTrivial p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.Vacuous
                    , depth
                    , logs
                    , state = toExecState p originalSubstitution unsupported
                    , nextStates = Nothing
                    , rule = Nothing
                    , unknownPredicate = Nothing
                    }
    RewriteCutPoint lbl _ p next ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.CutPointRule
                    , depth
                    , logs
                    , state = toExecState p originalSubstitution unsupported
                    , nextStates = Just [toExecState next originalSubstitution unsupported]
                    , rule = Just lbl
                    , unknownPredicate = Nothing
                    }
    RewriteTerminal lbl _ p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.TerminalRule
                    , depth
                    , logs
                    , state = toExecState p originalSubstitution unsupported
                    , nextStates = Nothing
                    , rule = Just lbl
                    , unknownPredicate = Nothing
                    }
    RewriteFinished _ _ p ->
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.DepthBound
                    , depth
                    , logs
                    , state = toExecState p originalSubstitution unsupported
                    , nextStates = Nothing
                    , rule = Nothing
                    , unknownPredicate = Nothing
                    }
    RewriteAborted failure p -> do
        Right $
            RpcTypes.Execute
                RpcTypes.ExecuteResult
                    { reason = RpcTypes.Aborted
                    , depth
                    , logs =
                        let abortRewriteLog =
                                mkLogRewriteTrace
                                    (logSuccessfulRewrites, logFailedRewrites)
                                    (logSuccessfulSimplifications, logFailedSimplifications)
                                    (RewriteStepFailed failure)
                         in logs <|> abortRewriteLog
                    , state = toExecState p originalSubstitution unsupported
                    , nextStates = Nothing
                    , rule = Nothing
                    , unknownPredicate = Nothing
                    }
  where
    logSuccessfulRewrites = fromMaybe False req.logSuccessfulRewrites
    logFailedRewrites = fromMaybe False req.logFailedRewrites
    logSuccessfulSimplifications = fromMaybe False req.logSuccessfulSimplifications
    logFailedSimplifications = fromMaybe False req.logFailedSimplifications
    depth = RpcTypes.Depth d

    logs =
        let traceLogs =
                concat . catMaybes . toList $
                    fmap
                        ( mkLogRewriteTrace
                            (logSuccessfulRewrites, logFailedRewrites)
                            (logSuccessfulSimplifications, logFailedSimplifications)
                        )
                        traces
            timingLog =
                fmap (ProcessingTime $ Just Booster) mbDuration
         in case (timingLog, traceLogs) of
                (Nothing, []) -> Nothing
                (Nothing, xs@(_ : _)) -> Just xs
                (Just t, xs) -> Just (t : xs)

toExecState :: Pattern -> Map Variable Term -> [Syntax.KorePattern] -> RpcTypes.ExecuteState
toExecState pat sub unsupported =
    RpcTypes.ExecuteState
        { term = addHeader t
        , predicate = addHeader <$> addUnsupported p
        , substitution = addHeader <$> s
        , ruleSubstitution = Nothing
        , rulePredicate = Nothing
        , ruleId = Nothing
        }
  where
    (t, p, s) = externalisePattern pat sub
    termSort = externaliseSort $ sortOfPattern pat
    allUnsupported = Syntax.KJAnd termSort unsupported
    addUnsupported
        | null unsupported = id
        | otherwise = maybe (Just allUnsupported) (Just . Syntax.KJAnd termSort . (: unsupported))

mkLogEquationTrace :: (Bool, Bool) -> ApplyEquations.EquationTrace () -> Maybe LogEntry
mkLogEquationTrace
    (logSuccessfulSimplifications, logFailedSimplifications) = \case
        ApplyEquations.EquationApplied _subjectTerm metadata _rewritten ->
            if logSuccessfulSimplifications
                then
                    Just $
                        Simplification
                            { originalTerm
                            , originalTermIndex
                            , origin
                            , result =
                                Success
                                    { rewrittenTerm = Nothing
                                    , substitution = Nothing
                                    , ruleId = fromMaybe "UNKNOWN" _ruleId
                                    }
                            }
                else Nothing
          where
            originalTerm = Nothing
            originalTermIndex = Nothing
            origin = Booster
            _ruleId = fmap getUniqueId metadata.ruleId
        ApplyEquations.EquationNotApplied _subjectTerm metadata result ->
            case result of
                ApplyEquations.Success rewrittenTrm
                    | logSuccessfulSimplifications ->
                        Just $
                            Simplification
                                { originalTerm
                                , originalTermIndex
                                , origin
                                , result =
                                    Success
                                        { rewrittenTerm =
                                            Just $ execStateToKoreJson $ toExecState (Pattern.Pattern_ rewrittenTrm) mempty mempty
                                        , substitution = Nothing
                                        , ruleId = fromMaybe "UNKNOWN" _ruleId
                                        }
                                }
                ApplyEquations.FailedMatch _failReason
                    | logFailedSimplifications ->
                        Just $
                            Simplification
                                { originalTerm
                                , originalTermIndex
                                , origin
                                , result = Failure{reason = "Failed match", _ruleId}
                                }
                ApplyEquations.IndeterminateMatch
                    | logFailedSimplifications ->
                        Just $
                            Simplification
                                { originalTerm
                                , originalTermIndex
                                , origin
                                , result = Failure{reason = "Indeterminate match", _ruleId}
                                }
                ApplyEquations.IndeterminateCondition _failedConditions
                    | logFailedSimplifications ->
                        Just $
                            Simplification
                                { originalTerm
                                , originalTermIndex
                                , origin
                                , result = Failure{reason = "Indeterminate side-condition", _ruleId}
                                }
                ApplyEquations.ConditionFalse{}
                    | logFailedSimplifications ->
                        Just $
                            Simplification
                                { originalTerm
                                , originalTermIndex
                                , origin
                                , result = Failure{reason = "Side-condition is false", _ruleId}
                                }
                ApplyEquations.RuleNotPreservingDefinedness
                    | logFailedSimplifications ->
                        Just $
                            Simplification
                                { originalTerm
                                , originalTermIndex
                                , origin
                                , result = Failure{reason = "The equation does not preserve definedness", _ruleId}
                                }
                ApplyEquations.MatchConstraintViolated _ varName
                    | logFailedSimplifications ->
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
            originalTerm = Nothing
            originalTermIndex = Nothing
            origin = Booster
            _ruleId = fmap getUniqueId metadata.ruleId

mkLogRewriteTrace ::
    (Bool, Bool) ->
    (Bool, Bool) ->
    RewriteTrace () ->
    Maybe [LogEntry]
mkLogRewriteTrace
    (logSuccessfulRewrites, logFailedRewrites)
    equationLogOpts@(logSuccessfulSimplifications, logFailedSimplifications) =
        \case
            RewriteSingleStep _ uid _ _res
                | logSuccessfulRewrites ->
                    Just $
                        singleton $
                            Rewrite
                                { result =
                                    Success
                                        { rewrittenTerm = Nothing
                                        , substitution = Nothing
                                        , ruleId = maybe "UNKNOWN" getUniqueId uid
                                        }
                                , origin = Booster
                                }
            RewriteBranchingStep _ _ -> Nothing -- we may or may not want to emit a trace here in the future
            RewriteStepFailed reason
                | logFailedRewrites ->
                    Just $
                        singleton $
                            Rewrite
                                { result = case reason of
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
                | logSuccessfulSimplifications || logFailedSimplifications ->
                    mapM (mkLogEquationTrace equationLogOpts) equationTraces
                | otherwise -> Just []
            RewriteSimplified equationTraces (Just failure)
                | logFailedSimplifications -> do
                    let final = singleton $ case failure of
                            ApplyEquations.IndexIsNone trm ->
                                Simplification
                                    { originalTerm = Just $ execStateToKoreJson $ toExecState (Pattern.Pattern_ trm) mempty mempty
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
                            ApplyEquations.TooManyRecursions stk ->
                                Simplification
                                    { originalTerm = Nothing
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result =
                                        Failure
                                            { reason =
                                                "Reached recursion limit of "
                                                    <> pack (show $ length stk)
                                            , _ruleId = Nothing
                                            }
                                    }
                            ApplyEquations.InternalError err ->
                                Simplification
                                    { originalTerm = Nothing
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result = Failure{reason = "Internal error: " <> err, _ruleId = Nothing}
                                    }
                            ApplyEquations.SideConditionFalse _predicate ->
                                Simplification
                                    { originalTerm = Nothing
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result = Failure{reason = "Side conditions false", _ruleId = Nothing}
                                    }
                            ApplyEquations.UndefinedTerm _t _err ->
                                Simplification
                                    { originalTerm = Nothing
                                    , originalTermIndex = Nothing
                                    , origin = Booster
                                    , result = Failure{reason = "Undefined term found", _ruleId = Nothing}
                                    }
                    (<> final) <$> mapM (mkLogEquationTrace equationLogOpts) equationTraces
                | otherwise -> Just []
            _ -> Nothing
