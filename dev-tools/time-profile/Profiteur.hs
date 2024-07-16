{-# LANGUAGE DeriveFunctor #-}

module Profiteur (module Profiteur) where

import Data.Aeson (FromJSON (..), Value (..))
import Data.HashMap.Strict qualified as HashMap
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe)
import Data.Sequence (Seq (..))
import Data.Set qualified as Set
import Data.Text (Text, pack)
import Data.Text qualified as Text
import Data.Vector qualified as Vector
import GHC.Generics (Generic)
import Profiteur.Core

import Kore.JsonRpc.Types.ContextLog

toId :: CLContext -> Text
toId = Text.replace " " "-" . pack . show

data LogMessage = LogMessage
    { context :: Seq CLContext
    , message :: Value
    , timestamp :: String
    }
    deriving (Generic, Show, FromJSON)

type AbortKey = (Text, Text)

newtype TimeMap timing = TimeMap (Map CLContext (timing, TimeMap timing))
    deriving newtype (Show, Monoid)
    deriving (Functor)

instance Monoid timing => Semigroup (TimeMap timing) where
    (TimeMap m1) <> (TimeMap m2) = TimeMap $ Map.unionWith (<>) m1 m2

(!) :: Monoid timing => TimeMap timing -> CLContext -> (timing, TimeMap timing)
(TimeMap m) ! c = fromMaybe mempty $ Map.lookup c m

aggregate :: Monoid a => TimeMap a -> a
aggregate (TimeMap m) = foldr (\(t, _) t' -> t <> t') mempty m

insertTime :: Seq CLContext -> Int -> Int -> TimeMap (Int, Int) -> TimeMap (Int, Int)
insertTime Empty _ _ m = m
insertTime (c :<| cs) t t' (TimeMap m) =
    TimeMap $
        let (minT, maxT, children'@(TimeMap childMap)) =
                case Map.lookup c m of
                    Nothing -> (t, t', insertTime cs t t' (TimeMap mempty))
                    Just ((minT', maxT'), children) -> (minT', maxT', insertTime cs t t' children)
         in Map.insert
                c
                (
                    ( foldr (\((minC, _), _) currentMin -> min minC currentMin) minT childMap
                    , foldr (\((_, maxC), _) currentMax -> max maxC currentMax) maxT childMap
                    )
                , children'
                )
                m

{- This function walks the parsed logs, collecting the timestamps and prodcing a timing map,
   which is a tree of contexts where each node holds the timing data for the subtree.AliasName
   this function generates the initial tree where each node holds the start and finis time of
   each log withing the context subtree.

   There are several subtle things to note here:
   *  We travese the logs with a lookahead, to figure out the interval between when the current and next message was emitted
      We store this interval in the tree and after traversal, compute the timing by calling `computeTimes`.
   *  This function produces a list of `TimeMap`s. THis is because we can have logs where certain contexts are repeated.
      This happens when we fall back from booster to kore for simplification and then re-attempt execution. This can result in the exact same context
      appearing twice during a single request. As a result, we check the current context and start a fresh timing map each time we encounter a proxy
      context, as we know this message signals a fallback.
      Note that this may still not be enitrely correct as there could be a context withing kore/booster that repeats within a request.
-}
collectTiming ::
    ([TimeMap (Int, Int)], Map UniqueId Text) ->
    LogMessage ->
    [LogMessage] ->
    ([TimeMap (Int, Int)], Map UniqueId Text)
collectTiming ([], ruleMap) l ls = collectTiming ([TimeMap mempty], ruleMap) l ls
collectTiming ((timeMap' : ts'), ruleMap) LogMessage{context, message, timestamp} nextLogs
    | t <- read timestamp =
        let newRuleMap =
                case context of
                    (_ :|> CLWithId (CtxRewrite ruleId) :|> CLNullary CtxDetail) | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
                    (_ :|> CLWithId (CtxFunction ruleId) :|> CLNullary CtxDetail) | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
                    (_ :|> CLWithId (CtxSimplification ruleId) :|> CLNullary CtxDetail) | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
                    _ -> ruleMap
            (timeMap, ts) = case context of
                (CLNullary CtxProxy :<| _) -> (TimeMap mempty, (timeMap' : ts'))
                _ -> (timeMap', ts')
            newTimeMap = case nextLogs of
                [] -> insertTime context t t timeMap
                LogMessage{timestamp = nextTimestamp} : _
                    | t' <- read nextTimestamp ->
                        insertTime context t t' timeMap
         in case nextLogs of
                [] -> ((newTimeMap : ts), newRuleMap)
                (l : ls) -> collectTiming ((newTimeMap : ts), newRuleMap) l ls

newtype ElapsedNanoseconds = ElapsedNanoseconds Int deriving newtype (Num, Show)

instance Semigroup ElapsedNanoseconds where
    (<>) = (+)

instance Monoid ElapsedNanoseconds where
    mempty = 0

newtype Count = Count Int deriving newtype (Num, Show)

instance Semigroup Count where
    (<>) = (+)

instance Monoid Count where
    mempty = 1

computeTimes :: TimeMap (Int, Int) -> TimeMap ElapsedNanoseconds
computeTimes = fmap $ \(minT, maxT) -> ElapsedNanoseconds $ maxT - minT

aggregateRewriteRulesPerRequest ::
    Map CLContext ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
    Map CLContext ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
    TimeMap (ElapsedNanoseconds, Count)
aggregateRewriteRulesPerRequest kore booster = TimeMap combinedMap
  where
    rewriteMap ::
        Map CLContext ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
        Map UniqueId (ElapsedNanoseconds, Count)
    rewriteMap =
        Map.foldrWithKey
            ( \k (_, TimeMap m') acc -> case k of
                CLWithId CtxTerm{} ->
                    Map.foldrWithKey
                        ( \k' ((t, c), _) acc' -> case k' of
                            CLWithId (CtxRewrite rId) -> case Map.lookup rId acc' of
                                Nothing -> Map.insert rId (t, 1) acc'
                                Just (totalT, count) -> Map.insert rId (totalT <> t, count + c) acc'
                            _ -> acc'
                        )
                        acc
                        m'
                _ -> acc
            )
            mempty

    rewriteMapKore' = rewriteMap kore
    rewriteMapBooster' = rewriteMap booster

    mkTimeMap c k m = case Map.lookup k m of
        Nothing -> Nothing
        Just tc -> Just (CLNullary c, (tc, mempty))

    combinedMapKeys = Set.toList $ Set.fromList $ Map.keys rewriteMapKore' <> Map.keys rewriteMapBooster'
    combinedMap =
        Map.fromList
            [ ( CLWithId $ CtxRewrite k
              , ( let combinedM =
                        TimeMap $
                            Map.fromList $
                                catMaybes [mkTimeMap CtxKore k rewriteMapKore', mkTimeMap CtxBooster k rewriteMapBooster']
                   in (aggregate combinedM, combinedM)
                )
              )
            | k <- combinedMapKeys
            ]

aggregateRewriteRulesPerRequest2 ::
    Map CLContext ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
    Map CLContext ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
    TimeMap (ElapsedNanoseconds, Count)
aggregateRewriteRulesPerRequest2 kore booster = TimeMap combinedMap2
  where
    rewriteMap ::
        Map CLContext ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
        Map UniqueId (ElapsedNanoseconds, Count)
    rewriteMap =
        Map.foldrWithKey
            ( \k (_, TimeMap m') acc -> case k of
                CLWithId CtxTerm{} ->
                    Map.foldrWithKey
                        ( \k' ((t, c), _) acc' -> case k' of
                            CLWithId (CtxRewrite rId) -> case Map.lookup rId acc' of
                                Nothing -> Map.insert rId (t, 1) acc'
                                Just (totalT, count) -> Map.insert rId (totalT <> t, count + c) acc'
                            _ -> acc'
                        )
                        acc
                        m'
                _ -> acc
            )
            mempty

    rewriteMapKore' = rewriteMap kore
    rewriteMapBooster' = rewriteMap booster

    rewriteMapKore = TimeMap $ Map.mapKeys (CLWithId . CtxRewrite) $ fmap (,mempty) rewriteMapKore'
    rewriteMapBooster = TimeMap $ Map.mapKeys (CLWithId . CtxRewrite) $ fmap (,mempty) rewriteMapBooster'

    combinedMap2 =
        Map.fromList
            [ (CLNullary CtxKore, (aggregate rewriteMapKore, rewriteMapKore))
            , (CLNullary CtxBooster, (aggregate rewriteMapBooster, rewriteMapBooster))
            ]

aggregateRewriteRules ::
    ( Map CLContext ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
      Map CLContext ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
      TimeMap (ElapsedNanoseconds, Count)
    ) ->
    TimeMap (ElapsedNanoseconds, Count) ->
    TimeMap (ElapsedNanoseconds, Count)
aggregateRewriteRules f (TimeMap requests) =
    TimeMap $
        Map.map
            ( \(_t, reqTimeMap) ->
                let TimeMap kore = snd $ (snd (reqTimeMap ! CLNullary CtxKore)) ! CLNullary CtxExecute
                    TimeMap booster = snd $ (snd (reqTimeMap ! CLNullary CtxBooster)) ! CLNullary CtxExecute
                    res = f kore booster
                 in (aggregate res, res)
            )
            requests

-- functions to convert a `TimeMap` into profiteur's `NodeMap`

toNode ::
    Map UniqueId Text -> [CLContext] -> CLContext -> ElapsedNanoseconds -> Count -> [CLContext] -> Node
toNode ruleMap ctxt currentCtxt (ElapsedNanoseconds t) (Count count) children =
    Node
        { nId = Text.intercalate "-" $ map toId $ ctxt <> [currentCtxt]
        , nName = toId currentCtxt
        , nModule = ""
        , nSrc = case currentCtxt of
            CLNullary{} -> ""
            CLWithId c -> fromMaybe "" $ getUniqueId c >>= flip Map.lookup ruleMap
        , nEntries = count
        , nTime = (fromIntegral t) / 1000000000
        , nAlloc = 0
        , nChildren =
            Vector.fromList
                [Text.intercalate "-" $ map toId $ ctxt <> [currentCtxt, c] | c <- children, filterNode c]
        }

filterNode :: CLContext -> Bool
filterNode = \case
    CLNullary CtxDetail -> False
    CLNullary CtxProxy -> False
    _ -> True

toNodes :: Int -> Map UniqueId Text -> [CLContext] -> TimeMap (ElapsedNanoseconds, Count) -> [Node]
toNodes cutoff ruleMap ctxt (TimeMap m) =
    concat
        [ (toNode ruleMap ctxt k t c (Map.keys cs))
            : if cutoff > 0 then toNodes (cutoff - 1) ruleMap (ctxt <> [k]) (TimeMap cs) else []
        | (k, ((t, c), TimeMap cs)) <- Map.toList m
        , filterNode k
        ]

toNodeMap :: TimeMap (ElapsedNanoseconds, Count) -> Map UniqueId Text -> NodeMap
toNodeMap tm@(TimeMap m) ruleMap =
    NodeMap
        (HashMap.fromList $ ("rpc-server", mainNode) : [(nId, n) | n@Node{nId} <- toNodes 10 ruleMap [] tm])
        "rpc-server"
  where
    (ElapsedNanoseconds time, Count count) = aggregate tm
    mainNode =
        Node
            { nId = "rpc-server"
            , nName = "rpc-server"
            , nModule = ""
            , nSrc = ""
            , nEntries = count
            , nTime = (fromIntegral time) / 1000000000
            , nAlloc = 0
            , nChildren =
                Vector.fromList [toId c | c <- Map.keys m, filterNode c]
            }
