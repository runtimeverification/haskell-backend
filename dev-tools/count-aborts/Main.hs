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
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Text (unpack)
import System.Environment (getArgs)
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
                    "To produce the correct context logs, run kore-rpc-booster with `--log-format json --log-file <file>`"
            | otherwise -> do
                let countContexts m f = foldl' (foldl' countAborts) m . map decode . BS.lines <$> BS.readFile f
                (counts, rIdTorLoc) <- foldM countContexts mempty files
                forM_ (sortOn (Down . snd) $ Map.toList counts) $ \(k, v) -> do
                    let (rType, rLoc) = fromMaybe ("-", "-") $ Map.lookup k rIdTorLoc
                    putStrLn $ unpack rType <> " " <> unpack k <> " | " <> unpack rLoc <> " | " <> show v
