module Types (module Types) where

import Data.Aeson (FromJSON (..), Value (..))
import Data.Aeson.Key (toString)
import Data.Aeson.KeyMap (toList)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Data.Text (Text, pack)
import GHC.Generics (Generic)
import Profiteur.Core
import qualified Data.Text as Text
import Data.Maybe (fromMaybe)
import qualified Data.Vector as Vector
import qualified Data.HashMap.Strict as HashMap
import Debug.Trace (trace)

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


newtype TimeMap = TimeMap (Map Context (Int, Int, TimeMap)) deriving newtype (Show, Semigroup, Monoid)


insertTime :: Seq Context -> Int -> TimeMap -> TimeMap
insertTime Empty _ m = m
insertTime (c :<| cs) t (TimeMap m) = TimeMap $ 
    let (minT, maxT, children'@(TimeMap childMap)) =
            case Map.lookup c m of
                Nothing -> (t,t, insertTime cs t mempty)
                Just (minT', maxT', children) -> (minT', maxT', insertTime cs t children)

    in Map.insert c (foldr (\(minC,_,_) currentMin -> min minC currentMin) minT childMap, foldr (\(_,maxC,_) currentMax -> max maxC currentMax) maxT childMap, children') m

collectTiming ::
    (TimeMap, Map Text Text) ->
    LogMessage ->
    (TimeMap, Map Text Text)
collectTiming (timeMap, ruleMap) lm@LogMessage{context, message, timestamp} =
    let newRuleMap =
            case context of
            (_ :|> Ref "rewrite" ruleId :|> Plain "detail") | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
            (_ :|> Ref "function" ruleId :|> Plain "detail") | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
            (_ :|> Ref "simplification" ruleId :|> Plain "detail") | String ruleLoc <- message -> Map.insert ruleId ruleLoc ruleMap
            _ -> ruleMap


        newTimeMap = insertTime (Plain "main" :<| context) (read timestamp) timeMap
    in (newTimeMap, newRuleMap)


toId :: Context -> Text
toId = \case
    Plain t -> t
    Ref k v -> k <> "-" <> v


toNode :: Map Text Text -> [Context] -> Context -> Int -> Int -> [Context] -> Node
toNode ruleMap ctxt currentCtxt minT maxT children = Node
    { nId = Text.intercalate "-" $ map toId $ ctxt <> [currentCtxt]
    , nName = toId currentCtxt
    , nModule = ""
    , nSrc = case currentCtxt of
        Plain{} -> ""
        Ref _ v -> fromMaybe "" (Map.lookup v ruleMap)
    , nEntries  = 0
    , nTime     = (fromIntegral $ maxT - minT) / 1000000
    , nAlloc    = 0
    , nChildren = Vector.fromList [Text.intercalate "-" $ map toId $ ctxt <> [currentCtxt, c] | c <- children]
    }


toNodes :: Int -> Map Text Text -> [Context] ->  TimeMap -> [Node]
toNodes levels ruleMap ctxt (TimeMap m) = concat [(toNode ruleMap ctxt k minT maxT (Map.keys cs)): if levels > 0 then toNodes (levels - 1) ruleMap (ctxt <> [k]) (TimeMap cs) else [] | (k, (minT, maxT, TimeMap cs)) <- Map.toList m]


toNodeMap :: TimeMap -> Map Text Text -> NodeMap
toNodeMap tm ruleMap = NodeMap (HashMap.fromList [(nId, n) | n@Node{nId} <- toNodes 100 ruleMap [] tm]) "main"