module Types (module Types) where

import Data.Aeson (FromJSON (..), Value (..))
import Data.Aeson.Key (toString)
import Data.Aeson.KeyMap (toList)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Sequence (Seq (..))
import Data.Text (Text, pack)
import GHC.Generics (Generic)

data Context = Plain Text | Ref Text Text deriving (Eq, Ord)

instance FromJSON Context where
    parseJSON (String t) = pure $ Plain t
    parseJSON (Object o) | [(k, String v)] <- toList o = pure $ Ref (pack $ toString k) v
    parseJSON _ = fail "Invalid context"

data LogMessage = LogMessage
    { context :: Seq Context
    , message :: Value
    }
    deriving (Generic, FromJSON)


countAborts :: (Map Text Int, Map Text (Text, Text)) -> LogMessage -> (Map Text Int, Map Text (Text, Text))
countAborts maps@(countMap, ruleMap) LogMessage{context, message} = case context of
    (_ :|> Ref "rewrite" ruleId :|> Plain "match" :|> Plain "abort") -> increment ruleId
    (_ :|> Ref "rewrite" ruleId :|> Plain "abort") -> increment ruleId
    (_ :|> Ref "function" ruleId :|> Plain "failure" :|> Plain "break") -> increment ruleId
    (_ :|> Ref "simplification" ruleId :|> Plain "failure" :|> Plain "break") -> increment ruleId
    (_ :|> Ref "function" ruleId :|> Plain "match" :|> Plain "failure" :|> Plain "break") -> increment ruleId
    (_ :|> Ref "simplification" ruleId :|> Plain "match" :|> Plain "failure" :|> Plain "break") -> increment ruleId
    (_ :|> Ref "rewrite" ruleId :|> Plain "detail") | String ruleLoc <- message -> (countMap, Map.insert ruleId ("rewrite", ruleLoc) ruleMap)
    (_ :|> Ref "function" ruleId :|> Plain "detail") | String ruleLoc <- message -> (countMap, Map.insert ruleId ("function", ruleLoc) ruleMap)
    (_ :|> Ref "simplification" ruleId :|> Plain "detail") | String ruleLoc <- message -> (countMap, Map.insert ruleId ("simplification", ruleLoc) ruleMap)
    _ -> maps
  where
    increment rid = (Map.alter (maybe (Just 1) (Just . (+ 1))) rid countMap, ruleMap)
