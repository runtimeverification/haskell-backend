module Types where

import Data.Text(Text, pack)
import Data.Aeson(Value(..), FromJSON(..), ToJSON(..), object, (.=))
import GHC.Generics (Generic)
import Data.Aeson.KeyMap (toList)
import Data.Aeson.Key (toString, fromText)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Sequence (Seq (..))


data Context = Plain Text | Ref Text Text deriving (Eq, Ord)


toText :: Context -> Text
toText = \case
  Plain t -> t
  Ref k v -> k <> " " <> v

instance FromJSON Context where
  parseJSON (String t) = pure $ Plain t
  parseJSON (Object o) | [(k, String v)] <- toList o = pure $ Ref (pack $ toString k) v 
  parseJSON _ = fail "Invalid context"

data LogMessage = LogMessage {
  context :: Seq Context,
  message :: Value
} deriving (Generic, FromJSON)


newtype Nested = Nested (Seq Value, Map Context Nested)

instance ToJSON Nested where
  toJSON (Nested (vs, m))
    | null vs = object m'
    | otherwise = object $ "logs" .= vs : m'
    where
      m' = [ (fromText $ toText k, toJSON v) | (k,v) <- Map.toList m]

insertAt :: Seq Context -> Value -> Nested -> Nested
insertAt Empty v (Nested (vs, nested)) = Nested (vs :|> v, nested)
insertAt (c :<| cs) v (Nested (vs, nested)) = 
  Nested (vs, flip (Map.insert c) nested $ insertAt cs v $ 
    case Map.lookup c nested of
      Nothing -> Nested mempty
      Just subtree -> subtree)

toNested :: Nested -> LogMessage -> Nested
toNested n LogMessage{context, message} =
  insertAt context message n


countAborts :: Map Text Int -> Seq Context -> Map Text Int
countAborts m = \case
  (_ :|> Ref "rewrite" ruleId :|> Plain "match" :|> Plain "abort") -> increment ruleId
  (_ :|> Ref "rewrite" ruleId :|> Plain "abort") -> increment ruleId
  _ -> m

  where
    increment rid = Map.alter (maybe (Just 1) (Just . (+1))) rid m