{- | Stand-alone parser executable for extracting timing information from JSON context logs

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

{- | Utility for parsing and extracting timing information from context logs,
   produced by running the booster binary with `-l Timing --log-format json --log-timestamps --timestamp-format nanosecond`.
   This tool collects the timing per each context level and uses the profiteur library to generate an HTML report of the timing information
   Call via `timing <path>.log`
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
                -- produce a timing map mirroring the context levels, roughly:
                -- main -> request n -> kore|booster -> execute|simplify|implies -> term rid -> rewrite id|simplification id|equation id -> success|failure
                writeReport h profFile $ toNodeMap timing ruleMap

            let htmlAggregateFile = profFile ++ ".aggregate.html"
            IO.withBinaryFile htmlAggregateFile IO.WriteMode $ \h -> do
                writeReport h profFile $
                    -- produce an agregate profile of all the number and total time spent trying each rewrite rule. The structure is:
                    -- main -> request n -> rewrite id -> kore|booster
                    toNodeMap (aggregateRewriteRules aggregateRewriteRulesPerRequest timing) ruleMap

            let htmlAggregateFile2 = profFile ++ ".aggregate2.html"
            IO.withBinaryFile htmlAggregateFile2 IO.WriteMode $ \h -> do
                writeReport h profFile $
                    -- produce an agregate profile of all the number and total time spent trying each rewrite rule. The structure is:
                    -- main -> request n -> kore|booster -> rewrite id
                    toNodeMap (aggregateRewriteRules aggregateRewriteRulesPerRequest2 timing) ruleMap
        _ -> error "invalid arguments"
