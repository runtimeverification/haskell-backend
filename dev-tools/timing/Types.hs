{-# LANGUAGE DeriveFunctor #-}

module Types (module Types) where

import Data.Aeson (FromJSON (..), Value (..))
import Data.Aeson.Key (toString)
import Data.Aeson.KeyMap (toList)
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

data Context = Plain Text | Ref Text Text deriving (Eq, Ord, Show)

instance FromJSON Context where
    parseJSON (String t) = pure $ Plain t
    parseJSON (Object o) | [(k, String v)] <- toList o = pure $ Ref (pack $ toString k) v
    parseJSON _ = fail "Invalid context"

data LogMessage = LogMessage
    { context :: Seq Context
    , message :: Value
    , timestamp :: String
    }
    deriving (Generic, Show, FromJSON)

type AbortKey = (Text, Text)

newtype TimeMap timing = TimeMap (Map Context (timing, TimeMap timing))
    deriving newtype (Show, Monoid)
    deriving (Functor)

instance Monoid timing => Semigroup (TimeMap timing) where
    (TimeMap m1) <> (TimeMap m2) = TimeMap $ Map.unionWith (<>) m1 m2

(!) :: Monoid timing => TimeMap timing -> Context -> (timing, TimeMap timing)
(TimeMap m) ! c = fromMaybe mempty $ Map.lookup c m

aggregate :: Monoid a => TimeMap a -> a
aggregate (TimeMap m) = foldr (\(t, _) t' -> t <> t') mempty m

insertTime :: Seq Context -> Int -> Int -> TimeMap (Int, Int) -> TimeMap (Int, Int)
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

collectTiming ::
    ([TimeMap (Int, Int)], Map Text Text) ->
    LogMessage ->
    [LogMessage] ->
    ([TimeMap (Int, Int)], Map Text Text)
collectTiming ([], ruleMap) l ls = collectTiming ([TimeMap mempty], ruleMap) l ls
collectTiming ((timeMap' : ts'), ruleMap) LogMessage{context, message, timestamp} nextLogs
    | t <- read timestamp =
        let newRuleMap =
                case context of
                    (_ :|> Ref "rewrite" ruleId :|> Plain "detail") | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
                    (_ :|> Ref "function" ruleId :|> Plain "detail") | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
                    (_ :|> Ref "simplification" ruleId :|> Plain "detail") | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
                    _ -> ruleMap
            (timeMap, ts) = case context of
                (Plain "proxy" :<| _) -> (TimeMap mempty, (timeMap' : ts'))
                _ -> (timeMap', ts')
            newTimeMap = case nextLogs of
                [] -> insertTime (Plain "main" :<| context) t t timeMap
                LogMessage{timestamp = nextTimestamp} : _
                    | t' <- read nextTimestamp ->
                        insertTime (Plain "main" :<| context) t t' timeMap
         in case nextLogs of
                [] -> ((newTimeMap : ts), newRuleMap)
                (l : ls) -> collectTiming ((newTimeMap : ts), newRuleMap) l ls

toId :: Context -> Text
toId = \case
    Plain t -> t
    Ref k v -> k <> "-" <> v

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

toNode :: Map Text Text -> [Context] -> Context -> ElapsedNanoseconds -> Count -> [Context] -> Node
toNode ruleMap ctxt currentCtxt (ElapsedNanoseconds t) (Count count) children =
    Node
        { nId = Text.intercalate "-" $ map toId $ ctxt <> [currentCtxt]
        , nName = toId currentCtxt
        , nModule = ""
        , nSrc = case currentCtxt of
            Plain{} -> ""
            Ref _ v -> fromMaybe "" (Map.lookup v ruleMap)
        , nEntries = count
        , nTime = (fromIntegral t) / 1000000000
        , nAlloc = 0
        , nChildren =
            Vector.fromList
                [Text.intercalate "-" $ map toId $ ctxt <> [currentCtxt, c] | c <- children, filterNode c]
        }

filterNode :: Context -> Bool
filterNode = \case
    Plain "detail" -> False
    Plain "proxy" -> False
    _ -> True

aggregateRewriteRulesPerRequest ::
    Map Context ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
    Map Context ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
    TimeMap (ElapsedNanoseconds, Count)
aggregateRewriteRulesPerRequest kore booster = TimeMap combinedMap
  where
    rewriteMap ::
        Map Context ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
        Map Text (ElapsedNanoseconds, Count)
    rewriteMap =
        Map.foldrWithKey
            ( \k (_, TimeMap m') acc -> case k of
                Ref "term" _tId ->
                    Map.foldrWithKey
                        ( \k' ((t, c), _) acc' -> case k' of
                            Ref "rewrite" rId -> case Map.lookup rId acc' of
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
        Just tc -> Just (Plain c, (tc, mempty))

    combinedMapKeys = Set.toList $ Set.fromList $ Map.keys rewriteMapKore' <> Map.keys rewriteMapBooster'
    combinedMap =
        Map.fromList
            [ ( Ref "rewrite" k
              , ( let combinedM =
                        TimeMap $
                            Map.fromList $
                                catMaybes [mkTimeMap "kore" k rewriteMapKore', mkTimeMap "booster" k rewriteMapBooster']
                   in (aggregate combinedM, combinedM)
                )
              )
            | k <- combinedMapKeys
            ]

aggregateRewriteRulesPerRequest2 ::
    Map Context ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
    Map Context ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
    TimeMap (ElapsedNanoseconds, Count)
aggregateRewriteRulesPerRequest2 kore booster = TimeMap combinedMap2
  where
    rewriteMap ::
        Map Context ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
        Map Text (ElapsedNanoseconds, Count)
    rewriteMap =
        Map.foldrWithKey
            ( \k (_, TimeMap m') acc -> case k of
                Ref "term" _tId ->
                    Map.foldrWithKey
                        ( \k' ((t, c), _) acc' -> case k' of
                            Ref "rewrite" rId -> case Map.lookup rId acc' of
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

    rewriteMapKore = TimeMap $ Map.mapKeys (Ref "rewrite") $ fmap (,mempty) rewriteMapKore'
    rewriteMapBooster = TimeMap $ Map.mapKeys (Ref "rewrite") $ fmap (,mempty) rewriteMapBooster'

    combinedMap2 =
        Map.fromList
            [ (Plain "kore", (aggregate rewriteMapKore, rewriteMapKore))
            , (Plain "booster", (aggregate rewriteMapBooster, rewriteMapBooster))
            ]

aggregateRewriteRules ::
    ( Map Context ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
      Map Context ((ElapsedNanoseconds, Count), TimeMap (ElapsedNanoseconds, Count)) ->
      TimeMap (ElapsedNanoseconds, Count)
    ) ->
    TimeMap (ElapsedNanoseconds, Count) ->
    TimeMap (ElapsedNanoseconds, Count)
aggregateRewriteRules f m =
    let TimeMap requests = snd (m ! Plain "main")
        requests' =
            TimeMap $
                Map.map
                    ( \(_t, reqTimeMap) ->
                        let TimeMap kore = snd $ (snd (reqTimeMap ! Plain "kore")) ! Plain "execute"
                            TimeMap booster = snd $ (snd (reqTimeMap ! Plain "booster")) ! Plain "execute"
                            res = f kore booster
                         in (aggregate res, res)
                    )
                    requests
     in TimeMap $ Map.fromList [(Plain "main", (aggregate requests', requests'))]

toNodes :: Int -> Map Text Text -> [Context] -> TimeMap (ElapsedNanoseconds, Count) -> [Node]
toNodes levels ruleMap ctxt (TimeMap m) =
    concat
        [ (toNode ruleMap ctxt k t c (Map.keys cs))
            : if levels > 0 then toNodes (levels - 1) ruleMap (ctxt <> [k]) (TimeMap cs) else []
        | (k, ((t, c), TimeMap cs)) <- Map.toList m
        , filterNode k
        ]

toNodeMap :: TimeMap (ElapsedNanoseconds, Count) -> Map Text Text -> NodeMap
toNodeMap tm ruleMap = NodeMap (HashMap.fromList [(nId, n) | n@Node{nId} <- toNodes 10 ruleMap [] tm]) "main"
