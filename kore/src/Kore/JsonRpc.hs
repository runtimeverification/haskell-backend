{-# LANGUAGE TemplateHaskell #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.JsonRpc (
    module Kore.JsonRpc,
) where

import Control.Concurrent.MVar qualified as MVar
import Control.Exception (ErrorCall (..), SomeException)
import Control.Monad.Catch (MonadCatch, handle)
import Control.Monad.Except (runExceptT)
import Control.Monad.Logger (logInfoN, runLoggingT)
import Data.Aeson.Types (ToJSON (..), Value (..))
import Data.Coerce (coerce)
import Data.Conduit.Network (serverSettings)
import Data.IORef (readIORef)
import Data.InternedText (globalInternedTextCache)
import Data.Limit (Limit (..))
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import GlobalMain (
    LoadedDefinition (..),
    SerializedDefinition (..),
 )
import Kore.Attribute.Symbol (StepperAttributes)
import Kore.Builtin qualified as Builtin
import Kore.Error (Error (..))
import Kore.Exec qualified as Exec
import Kore.Exec.GraphTraversal qualified as GraphTraversal
import Kore.IndexedModule.MetadataTools (SmtMetadataTools)
import Kore.IndexedModule.MetadataToolsBuilder qualified as MetadataTools
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (Pattern)
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (pattern PredicateTrue)
import Kore.Internal.TermLike (TermLike)
import Kore.Internal.TermLike qualified as TermLike
import Kore.JsonRpc.Server (ErrorObj (..), JsonRpcHandler (JsonRpcHandler), Request (getReqId), Respond, jsonRpcServer)
import Kore.JsonRpc.Types
import Kore.Log.DecidePredicateUnknown (DecidePredicateUnknown, srcLoc)
import Kore.Log.InfoExecDepth (ExecDepth (..))
import Kore.Log.InfoJsonRpcProcessRequest (InfoJsonRpcProcessRequest (..))
import Kore.Log.JsonRpc (LogJsonRpcServer (..))
import Kore.Parser (parseKoreDefinition)
import Kore.Reachability.Claim qualified as Claim
import Kore.Rewrite (
    ProgramState,
    extractProgramState,
 )
import Kore.Rewrite.ClaimPattern qualified as ClaimPattern
import Kore.Rewrite.RewritingVariable (
    getRewritingVariable,
    mkRewritingPattern,
    mkRewritingTerm,
 )
import Kore.Rewrite.SMT.Evaluator qualified as SMT.Evaluator
import Kore.Rewrite.SMT.Lemma (getSMTLemmas)
import Kore.Rewrite.Timeout (
    EnableMovingAverage (..),
    StepTimeout (..),
 )
import Kore.Simplify.API (evalSimplifier)
import Kore.Simplify.Pattern qualified as Pattern
import Kore.Simplify.Simplify (Simplifier)
import Kore.Syntax (VariableName)
import Kore.Syntax.Json qualified as PatternJson
import Kore.Syntax.Module (ModuleName (..))
import Kore.Syntax.Sentence (
    SentenceAxiom,
 )
import Kore.Validate.DefinitionVerifier (verifyAndIndexDefinitionWithBase)
import Kore.Validate.PatternVerifier qualified as PatternVerifier
import Log qualified
import Prelude.Kore
import Pretty (Pretty)
import Pretty qualified
import SMT qualified

respond ::
    forall m.
    MonadIO m =>
    MonadCatch m =>
    MVar.MVar ServerState ->
    ModuleName ->
    ( forall a.
      SmtMetadataTools StepperAttributes ->
      [SentenceAxiom (TermLike VariableName)] ->
      SMT.SMT a ->
      IO a
    ) ->
    Respond (API 'Req) m (API 'Res)
respond serverState moduleName runSMT =
    withErrHandler . \case
        Execute ExecuteRequest{state, maxDepth, _module, cutPointRules, terminalRules, movingAverageStepTimeout, stepTimeout} -> withMainModule (coerce _module) $ \serializedModule lemmas ->
            case PatternVerifier.runPatternVerifier (verifierContext serializedModule) $
                PatternVerifier.verifyStandalonePattern Nothing $
                    PatternJson.toParsedPattern $
                        PatternJson.term state of
                Left err -> pure $ Left $ couldNotVerify $ toJSON err
                Right verifiedPattern -> do
                    traversalResult <-
                        liftIO
                            ( runSMT (Exec.metadataTools serializedModule) lemmas $
                                Exec.rpcExec
                                    (maybe Unlimited (\(Depth n) -> Limit n) maxDepth)
                                    (coerce stepTimeout)
                                    ( if fromMaybe False movingAverageStepTimeout
                                        then EnableMovingAverage
                                        else DisableMovingAverage
                                    )
                                    serializedModule
                                    (toStopLabels cutPointRules terminalRules)
                                    verifiedPattern
                            )

                    pure $ buildResult (TermLike.termLikeSort verifiedPattern) traversalResult
          where
            toStopLabels :: Maybe [Text] -> Maybe [Text] -> Exec.StopLabels
            toStopLabels cpRs tRs =
                Exec.StopLabels (fromMaybe [] cpRs) (fromMaybe [] tRs)

            buildResult ::
                TermLike.Sort ->
                GraphTraversal.TraversalResult (Exec.RpcExecState TermLike.VariableName) ->
                Either ErrorObj (API 'Res)
            buildResult sort = \case
                GraphTraversal.Ended
                    [Exec.RpcExecState{rpcDepth = ExecDepth depth, rpcProgState = result}] ->
                        -- Actually not "ended" but out of instructions.
                        -- See @toTransitionResult@ in @rpcExec@.
                        Right $
                            Execute $
                                ExecuteResult
                                    { state = patternToExecState sort result
                                    , depth = Depth depth
                                    , reason = DepthBound
                                    , rule = Nothing
                                    , nextStates = Nothing
                                    }
                GraphTraversal.GotStuck
                    _n
                    [Exec.RpcExecState{rpcDepth = ExecDepth depth, rpcProgState = result}] ->
                        Right $
                            Execute $
                                ExecuteResult
                                    { state = patternToExecState sort result
                                    , depth = Depth depth
                                    , reason = Stuck
                                    , rule = Nothing
                                    , nextStates = Nothing
                                    }
                GraphTraversal.Stopped
                    [Exec.RpcExecState{rpcDepth = ExecDepth depth, rpcProgState, rpcRule = Nothing}]
                    nexts ->
                        Right $
                            Execute $
                                ExecuteResult
                                    { state = patternToExecState sort rpcProgState
                                    , depth = Depth depth
                                    , reason = Branching
                                    , rule = Nothing
                                    , nextStates =
                                        Just $ map (patternToExecState sort . Exec.rpcProgState) nexts
                                    }
                GraphTraversal.Stopped
                    [Exec.RpcExecState{rpcDepth = ExecDepth depth, rpcProgState, rpcRule = Just lbl}]
                    nexts
                        | lbl `elem` fromMaybe [] cutPointRules ->
                            Right $
                                Execute $
                                    ExecuteResult
                                        { state = patternToExecState sort rpcProgState
                                        , depth = Depth depth
                                        , reason = CutPointRule
                                        , rule = Just lbl
                                        , nextStates =
                                            Just $ map (patternToExecState sort . Exec.rpcProgState) nexts
                                        }
                        | lbl `elem` fromMaybe [] terminalRules ->
                            Right $
                                Execute $
                                    ExecuteResult
                                        { state = patternToExecState sort rpcProgState
                                        , depth = Depth depth
                                        , reason = TerminalRule
                                        , rule = Just lbl
                                        , nextStates = Nothing
                                        }
                GraphTraversal.TimedOut
                    Exec.RpcExecState{rpcDepth = ExecDepth depth, rpcProgState}
                    _ ->
                        Right $
                            Execute $
                                ExecuteResult
                                    { state = patternToExecState sort rpcProgState
                                    , depth = Depth depth
                                    , reason = Timeout
                                    , rule = Nothing
                                    , nextStates = Nothing
                                    }
                -- these are programmer errors
                result@GraphTraversal.Aborted{} ->
                    Left $ serverError "aborted" $ asText (show result)
                other ->
                    Left $ serverError "multiple states in result" $ asText (show other)

            patternToExecState ::
                TermLike.Sort ->
                ProgramState (Pattern TermLike.VariableName) ->
                ExecuteState
            patternToExecState sort s =
                ExecuteState
                    { term =
                        PatternJson.fromTermLike $ Pattern.term p
                    , substitution =
                        PatternJson.fromSubstitution sort $ Pattern.substitution p
                    , predicate =
                        case Pattern.predicate p of
                            PredicateTrue -> Nothing
                            pr -> Just $ PatternJson.fromPredicate sort pr
                    }
              where
                p = fromMaybe (Pattern.bottomOf sort) $ extractProgramState s

        -- Step StepRequest{} -> pure $ Right $ Step $ StepResult []
        Implies ImpliesRequest{antecedent, consequent, _module} -> withMainModule (coerce _module) $ \serializedModule lemmas ->
            case PatternVerifier.runPatternVerifier (verifierContext serializedModule) verify of
                Left err ->
                    pure $ Left $ couldNotVerify $ toJSON err
                Right (antVerified, consVerified) -> do
                    let leftPatt =
                            mkRewritingPattern $ Pattern.parsePatternFromTermLike antVerified
                        sort = TermLike.termLikeSort antVerified
                        (consWOExistentials, existentialVars) =
                            ClaimPattern.termToExistentials $
                                mkRewritingTerm consVerified
                        rightPatt = Pattern.parsePatternFromTermLike consWOExistentials

                    result <-
                        liftIO
                            . runSMT (Exec.metadataTools serializedModule) lemmas
                            . (evalInSimplifierContext serializedModule)
                            . runExceptT
                            $ Claim.checkSimpleImplication
                                leftPatt
                                rightPatt
                                existentialVars
                    pure $ buildResult sort result
          where
            verify = do
                antVerified <-
                    PatternVerifier.verifyStandalonePattern Nothing $
                        PatternJson.toParsedPattern $
                            PatternJson.term antecedent
                consVerified <-
                    PatternVerifier.verifyStandalonePattern Nothing $
                        PatternJson.toParsedPattern $
                            PatternJson.term consequent
                pure (antVerified, consVerified)

            renderCond sort cond =
                let pat = Condition.mapVariables getRewritingVariable cond
                    predicate =
                        PatternJson.fromPredicate sort $ Condition.predicate pat
                    mbSubstitution =
                        PatternJson.fromSubstitution sort $ Condition.substitution pat
                    noSubstitution = PatternJson.fromTermLike $ TermLike.mkTop sort
                 in Condition
                        { predicate
                        , substitution = fromMaybe noSubstitution mbSubstitution
                        }

            buildResult _ (Left err) = Left $ implicationError $ toJSON err
            buildResult sort (Right (term, r)) =
                let jsonTerm =
                        PatternJson.fromTermLike $
                            TermLike.mapVariables getRewritingVariable term
                 in Right . Implies $
                        case r of
                            Claim.Implied Nothing ->
                                ImpliesResult jsonTerm True (Just . renderCond sort $ Condition.bottom)
                            Claim.Implied (Just cond) ->
                                ImpliesResult jsonTerm True (Just . renderCond sort $ cond)
                            Claim.NotImplied _ ->
                                ImpliesResult jsonTerm False Nothing
                            Claim.NotImpliedStuck (Just cond) ->
                                let jsonCond = renderCond sort cond
                                 in ImpliesResult jsonTerm False (Just jsonCond)
                            Claim.NotImpliedStuck Nothing ->
                                ImpliesResult jsonTerm False (Just . renderCond sort $ Condition.bottom)
        Simplify SimplifyRequest{state, _module} -> withMainModule (coerce _module) $ \serializedModule lemmas ->
            case PatternVerifier.runPatternVerifier (verifierContext serializedModule) verifyState of
                Left err ->
                    pure $ Left $ couldNotVerify $ toJSON err
                Right stateVerified -> do
                    let patt =
                            mkRewritingPattern $ Pattern.parsePatternFromTermLike stateVerified
                        sort = TermLike.termLikeSort stateVerified

                    result <-
                        liftIO
                            . runSMT (Exec.metadataTools serializedModule) lemmas
                            . (evalInSimplifierContext serializedModule)
                            $ SMT.Evaluator.filterMultiOr $srcLoc =<< Pattern.simplify patt

                    pure $
                        Right $
                            Simplify
                                SimplifyResult
                                    { state =
                                        PatternJson.fromTermLike $
                                            TermLike.mapVariables getRewritingVariable $
                                                OrPattern.toTermLike sort result
                                    }
          where
            verifyState =
                PatternVerifier.verifyStandalonePattern Nothing $
                    PatternJson.toParsedPattern $
                        PatternJson.term state
        AddModule AddModuleRequest{name, _module} ->
            case parseKoreDefinition "" _module of
                Left err -> pure . Left . couldNotParse $ toJSON err
                Right parsedModule -> do
                    LoadedDefinition{indexedModules, definedNames, kFileLocations} <-
                        liftIO $ loadedDefinition <$> MVar.readMVar serverState
                    let verified =
                            verifyAndIndexDefinitionWithBase
                                (indexedModules, definedNames)
                                Builtin.koreVerifiers
                                parsedModule
                    case verified of
                        Left err -> pure . Left . couldNotVerify $ toJSON err
                        Right (indexedModules', definedNames') ->
                            case Map.lookup (coerce name) indexedModules' of
                                Nothing -> pure . Left . couldNotFindModule $ toJSON name
                                Just mainModule -> do
                                    let metadataTools = MetadataTools.build mainModule
                                        lemmas = getSMTLemmas mainModule

                                    serializedModule' <-
                                        liftIO
                                            . runSMT metadataTools lemmas
                                            $ Exec.makeSerializedModule mainModule

                                    internedTextCache <- liftIO $ readIORef globalInternedTextCache

                                    liftIO . MVar.modifyMVar_ serverState $
                                        \ServerState{serializedModules} -> do
                                            let serializedDefinition =
                                                    SerializedDefinition
                                                        { serializedModule = serializedModule'
                                                        , locations = kFileLocations
                                                        , internedTextCache
                                                        , lemmas
                                                        }
                                                loadedDefinition =
                                                    LoadedDefinition
                                                        { indexedModules = indexedModules'
                                                        , definedNames = definedNames'
                                                        , kFileLocations
                                                        }
                                            pure
                                                ServerState
                                                    { serializedModules =
                                                        Map.insert (coerce name) serializedDefinition serializedModules
                                                    , loadedDefinition
                                                    }

                                    pure . Right $ AddModule ()

        -- this case is only reachable if the cancel appeared as part of a batch request
        Cancel -> pure $ Left $ ErrorObj "Cancel request unsupported in batch mode" (-32001) Null
  where
    withMainModule module' act = do
        let mainModule = fromMaybe moduleName module'
        ServerState{serializedModules} <- liftIO $ MVar.readMVar serverState
        case Map.lookup mainModule serializedModules of
            Nothing -> pure . Left . couldNotFindModule $ toJSON mainModule
            Just (SerializedDefinition{serializedModule, lemmas}) ->
                act serializedModule lemmas

    couldNotVerify err = ErrorObj "Could not verify KORE pattern" (-32002) err

    couldNotParse err = ErrorObj "Could not parse KORE pattern" (-32004) err

    couldNotFindModule err = ErrorObj "Could not find module" (-32005) err

    asText :: Pretty.Pretty a => a -> Value
    asText = String . Pretty.renderText . Pretty.layoutOneLine . Pretty.pretty

    implicationError err = ErrorObj "Implication check error" (-32003) err

    -- catch all calls to `error` that may occur within the guts of the engine
    withErrHandler ::
        m (Either ErrorObj res) ->
        m (Either ErrorObj res)
    withErrHandler =
        let mkError (ErrorCallWithLocation msg loc) =
                Error{errorContext = [loc], errorError = msg}
         in handle (pure . Left . serverError "crashed" . toJSON . mkError)

    verifierContext Exec.SerializedModule{verifiedModule} =
        PatternVerifier.verifiedModuleContext verifiedModule
            & PatternVerifier.withBuiltinVerifiers Builtin.koreVerifiers

    evalInSimplifierContext :: Exec.SerializedModule -> Simplifier a -> SMT.SMT a
    evalInSimplifierContext
        Exec.SerializedModule
            { sortGraph
            , overloadGraph
            , metadataTools
            , verifiedModule
            , equations
            } =
            evalSimplifier
                verifiedModule
                sortGraph
                overloadGraph
                metadataTools
                equations

serverError :: String -> Value -> ErrorObj
serverError detail payload =
    ErrorObj ("Server error: " <> detail) (-32032) payload

data ServerState = ServerState
    { serializedModules :: Map.Map ModuleName SerializedDefinition
    , loadedDefinition :: LoadedDefinition
    }

runServer ::
    Int ->
    MVar.MVar ServerState ->
    ModuleName ->
    ( forall a.
      SmtMetadataTools StepperAttributes ->
      [SentenceAxiom (TermLike VariableName)] ->
      SMT.SMT a ->
      IO a
    ) ->
    Log.LoggerEnv IO ->
    IO ()
runServer port serverState mainModule runSMT Log.LoggerEnv{logAction} = do
    flip runLoggingT logFun $
        jsonRpcServer
            srvSettings
            (\req parsed -> log (InfoJsonRpcProcessRequest (getReqId req) parsed) >> respond serverState mainModule runSMT parsed)
            [ JsonRpcHandler $ \(err :: DecidePredicateUnknown) ->
                let mkPretty = Pretty.renderText . Pretty.layoutPretty Pretty.defaultLayoutOptions . Pretty.pretty
                 in logInfoN (mkPretty err) >> pure (serverError "crashed" $ toJSON $ mkPretty err)
            , JsonRpcHandler $ \(err :: SomeException) -> logInfoN (Text.pack $ show err) >> pure (serverError "crashed" $ toJSON $ show err)
            ]
  where
    srvSettings = serverSettings port "*"

    logFun loc src level msg =
        Log.logWith logAction $ LogJsonRpcServer{loc, src, level, msg}

    log :: MonadIO m => Log.Entry entry => entry -> m ()
    log = Log.logWith $ Log.hoistLogAction liftIO logAction
