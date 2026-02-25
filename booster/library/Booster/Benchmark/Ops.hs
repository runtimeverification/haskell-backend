{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Benchmark operations layered on top of existing booster implementation paths.
-}
module Booster.Benchmark.Ops (
    runMapLookup,
    runMapUpdate,
    runMapRemove,
    runMapInKeys,
    runMapKeys,
    runMapValues,
    runMapSize,
    runListGet,
    runListSize,
    runListRange,
    runListConcat,
    ksetIn,
    ksetSize,
    ksetDifference,
    ksetUnion,
    ksetIntersection,
    matchMapTerms,
    compareTermHashFirst,
    substituteMap,
    runPipelineOnce,
) where

import Control.Monad.Logger (runNoLoggingT)
import Control.Monad.Trans.Except (runExcept)
import Data.ByteString (ByteString)
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text

import Booster.Benchmark.Data
import Booster.Builtin qualified as Builtin
import Booster.Builtin.INT (intTerm)
import Booster.Pattern.ApplyEquations (Direction (TopDown), evaluateTerm)
import Booster.Pattern.Base
import Booster.Pattern.Match (MatchResult (..), MatchType (Rewrite), matchTerms)
import Booster.Pattern.Substitution (substituteInTerm)
import Booster.SMT.Interface (noSolver)
import Booster.Syntax.Json.Externalise (externaliseTerm)
import Booster.Syntax.Json.Internalise (
    internaliseTerm,
    pattern DisallowAlias,
    pattern IgnoreSubsorts,
 )

runMapLookup :: Term -> Term -> Either Text (Maybe Term)
runMapLookup mapTerm key = runHook "MAP.lookup" [mapTerm, key]

runMapUpdate :: Term -> Term -> Term -> Either Text (Maybe Term)
runMapUpdate mapTerm key value = runHook "MAP.update" [mapTerm, key, value]

runMapRemove :: Term -> Term -> Either Text (Maybe Term)
runMapRemove mapTerm key = runHook "MAP.remove" [mapTerm, key]

runMapInKeys :: Term -> Term -> Either Text (Maybe Term)
runMapInKeys mapTerm key = runHook "MAP.in_keys" [key, mapTerm]

runMapKeys :: Term -> Either Text (Maybe Term)
runMapKeys mapTerm = runHook "MAP.keys_list" [mapTerm]

runMapValues :: Term -> Either Text (Maybe Term)
runMapValues mapTerm = runHook "MAP.values" [mapTerm]

runMapSize :: Term -> Either Text (Maybe Term)
runMapSize mapTerm = runHook "MAP.size" [mapTerm]

runListGet :: Term -> Int -> Either Text (Maybe Term)
runListGet listTerm idx = runHook "LIST.get" [listTerm, intTerm (fromIntegral idx)]

runListSize :: Term -> Either Text (Maybe Term)
runListSize listTerm = runHook "LIST.size" [listTerm]

runListRange :: Term -> Int -> Int -> Either Text (Maybe Term)
runListRange listTerm front back =
    runHook
        "LIST.range"
        [ listTerm
        , intTerm (fromIntegral front)
        , intTerm (fromIntegral back)
        ]

runListConcat :: Term -> Term -> Either Text (Maybe Term)
runListConcat left right = runHook "LIST.concat" [left, right]

ksetIn :: Term -> Term -> Bool
ksetIn element (KSet _ elements Nothing) = element `elem` elements
ksetIn _ _ = False

ksetSize :: Term -> Int
ksetSize (KSet _ elements Nothing) = length elements
ksetSize _ = 0

ksetDifference :: Term -> Term -> Term
ksetDifference left right =
    case (left, right) of
        (KSet def leftElements Nothing, KSet _ rightElements Nothing) ->
            KSet def (Set.toList $ Set.fromList leftElements `Set.difference` Set.fromList rightElements) Nothing
        _ -> left

ksetUnion :: Term -> Term -> Term
ksetUnion left right =
    case (left, right) of
        (KSet def leftElements Nothing, KSet _ rightElements Nothing) ->
            KSet def (Set.toList $ Set.fromList leftElements `Set.union` Set.fromList rightElements) Nothing
        _ -> left

ksetIntersection :: Term -> Term -> Term
ksetIntersection left right =
    case (left, right) of
        (KSet def leftElements Nothing, KSet _ rightElements Nothing) ->
            KSet def (Set.toList $ Set.fromList leftElements `Set.intersection` Set.fromList rightElements) Nothing
        _ -> left

matchMapTerms :: Term -> Term -> MatchResult
matchMapTerms = matchTerms Rewrite benchmarkDefinition

compareTermHashFirst :: Term -> Term -> Ordering
compareTermHashFirst left right =
    case compare (getAttributes left).hash (getAttributes right).hash of
        EQ -> compare left right
        ord -> ord

substituteMap :: Substitution -> Term -> Term
substituteMap = substituteInTerm

runPipelineOnce :: IO (Either Text Int)
runPipelineOnce = runNoLoggingT $ do
    solver <- noSolver
    let externalSubject = externaliseTerm pipelineSubjectTerm
    case runExcept (internaliseTerm DisallowAlias IgnoreSubsorts Nothing benchmarkDefinition externalSubject) of
        Left err ->
            pure $ Left ("pipeline internalise failed: " <> Text.pack (show err))
        Right internalisedSubject ->
            case matchTerms Rewrite benchmarkDefinition pipelinePatternTerm internalisedSubject of
                MatchSuccess substitution -> do
                    let substituted = substituteInTerm substitution pipelineRhsTerm
                    (evaluated, _cache) <-
                        evaluateTerm TopDown benchmarkDefinition Nothing solver mempty mempty substituted
                    case evaluated of
                        Left err ->
                            pure $ Left ("pipeline evaluate failed: " <> Text.pack (show err))
                        Right rewritten -> do
                            let externalised = externaliseTerm rewritten
                            pure $ Right (length (show externalised))
                other ->
                    pure $ Left ("pipeline match failed: " <> Text.pack (show other))

runHook :: ByteString -> [Term] -> Either Text (Maybe Term)
runHook hookName args =
    case Map.lookup hookName Builtin.hooks of
        Nothing ->
            Left ("missing builtin hook: " <> Text.pack (show hookName))
        Just hook ->
            firstError (runExcept (hook args))

firstError :: Show e => Either e a -> Either Text a
firstError = either (Left . Text.pack . show) Right
