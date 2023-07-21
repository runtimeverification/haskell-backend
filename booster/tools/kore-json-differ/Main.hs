{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Main (main) where

import Data.ByteString.Lazy.Char8 qualified as BS
import System.Environment (getArgs)
import System.Exit

import Booster.JsonRpc.Utils

usage :: String
usage =
    unlines
        [ "Display differences between two json files containing kore-rpc data"
        , ""
        , "Usage:"
        , "       <program-name> [--help | KOREJSON1 KOREJSON2]"
        , ""
        , "where KOREJSON<N> are paths to files containing a kore-rpc JSON request"
        , "a kore-rpc JSON response, a kore term in JSON format, or other JSON."
        ]

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] ->
            putStrLn usage
        _
            | "--help" `elem` args ->
                putStrLn usage
        [x, y] -> do
            result <- diffJson x y
            BS.putStrLn $ renderResult x y result
            exitWith $ if isIdentical result then ExitSuccess else ExitFailure 1
        _other -> do
            putStrLn $ "ERROR: program requires exactly two arguments.\n\n" <> usage
            exitWith $ ExitFailure 2
