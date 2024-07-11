{-# LANGUAGE PatternSynonyms #-}

{- | Stand-alone parser executable for testing and profiling

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Control.Monad (foldM, forM_)
import Data.Aeson (decode)
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.List (foldl', sortOn)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Sequence (Seq (..))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Environment (getArgs)

import Kore.JsonRpc.Types.ContextLog

{- | Utility for parsing and extracting information from context logs,
   produced by running the booster binary with `--log-format json --log-file <path>`.
   This tool collects the number of aborts for each rewrite rule and displays the informantion in a table.
   Call via `count-aborts <path_1> ... <path_n>`
-}
main :: IO ()
main =
    getArgs >>= \case
        files
            | "-h" `elem` files || "--help" `elem` files -> do
                putStrLn
                    "This tool parses the JSON contextual logs, collects the number of aborts for each rewrite rule and displays the informantion in a table."
                putStrLn "Call via `count-aborts <path_1> ... <path_n>`"
                putStrLn
                    "To produce the correct context logs, run kore-rpc-booster with `-l Aborts --log-format json --log-file <file>`"
            | otherwise -> do
                let countContexts m f = foldl' (foldl' countAborts) m . map decode . BS.lines <$> BS.readFile f
                (counts, rIdTorLoc) <- foldM countContexts mempty files
                forM_ (sortOn (Down . snd) $ Map.toList counts) $ \((rule, reason), count) -> do
                    let (rType, rLoc) = fromMaybe ("-", "-") $ Map.lookup rule rIdTorLoc
                    T.putStrLn . T.unwords $
                        map ("| " <>) [rType <> " " <> T.pack (show rule), rLoc, T.pack (show reason), T.pack (show count)]

type AbortKey = (UniqueId, SimpleContext)

pattern CRewrite, CFunction, CSimpl :: UniqueId -> CLContext
pattern CRewrite r = CLWithId (CtxRewrite r)
pattern CFunction r = CLWithId (CtxFunction r)
pattern CSimpl r = CLWithId (CtxSimplification r)

pattern C :: SimpleContext -> CLContext
pattern C ctx = CLNullary ctx

countAborts ::
    (Map AbortKey Int, Map UniqueId (Text, Text)) ->
    LogLine ->
    (Map AbortKey Int, Map UniqueId (Text, Text))
countAborts maps@(countMap, ruleMap) LogLine{context, message} = case context of
    (_ :|> CRewrite ruleId :|> C reason :|> C CtxAbort) -> increment reason ruleId
    (_ :|> CFunction ruleId :|> C CtxFailure :|> C CtxBreak) -> increment CtxFailure ruleId
    (_ :|> CSimpl ruleId :|> C CtxFailure :|> C CtxBreak) -> increment CtxFailure ruleId
    (_ :|> CFunction ruleId :|> C CtxMatch :|> C CtxFailure :|> C CtxBreak) -> increment CtxFailure ruleId
    (_ :|> CSimpl ruleId :|> C CtxMatch :|> C CtxFailure :|> C CtxBreak) -> increment CtxFailure ruleId
    (_ :|> CRewrite ruleId :|> C CtxDetail) | CLText ruleLoc <- message -> (countMap, Map.insert ruleId ("rewrite", ruleLoc) ruleMap)
    (_ :|> CFunction ruleId :|> C CtxDetail) | CLText ruleLoc <- message -> (countMap, Map.insert ruleId ("function", ruleLoc) ruleMap)
    (_ :|> CSimpl ruleId :|> C CtxDetail) | CLText ruleLoc <- message -> (countMap, Map.insert ruleId ("simplification", ruleLoc) ruleMap)
    _ -> maps
  where
    increment rsn rid = (Map.alter (maybe (Just 1) (Just . (+ 1))) (rid, rsn) countMap, ruleMap)
