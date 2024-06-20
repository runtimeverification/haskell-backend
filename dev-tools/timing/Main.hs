{- | Stand-alone parser executable for testing and profiling

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Data.Aeson (decode)
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.Maybe (mapMaybe)
import Profiteur.Main (writeReport)
import System.Environment (getArgs)
import System.IO qualified as IO
import Types

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
        [profFile] -> do
            logs <- mapMaybe decode . BS.lines <$> BS.readFile profFile

            let (timings, ruleMap) = case logs of
                    m : ms -> collectTiming mempty m ms
                    [] -> mempty
                timing = foldr (((<>)) . fmap (,Count 1) . computeTimes) (TimeMap mempty) timings
                htmlFile = profFile ++ ".html"
            IO.withBinaryFile htmlFile IO.WriteMode $ \h -> do
                writeReport h profFile $ toNodeMap timing ruleMap

            let htmlAggregateFile = profFile ++ ".aggregate.html"
            IO.withBinaryFile htmlAggregateFile IO.WriteMode $ \h -> do
                writeReport h profFile $
                    toNodeMap (aggregateRewriteRules aggregateRewriteRulesPerRequest timing) ruleMap

            let htmlAggregateFile2 = profFile ++ ".aggregate2.html"
            IO.withBinaryFile htmlAggregateFile2 IO.WriteMode $ \h -> do
                writeReport h profFile $
                    toNodeMap (aggregateRewriteRules aggregateRewriteRulesPerRequest2 timing) ruleMap
        _ -> error "invalid arguments"
