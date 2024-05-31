{- | Stand-alone parser executable for testing and profiling

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Control.Monad (foldM, forM_)
import Data.Aeson (ToJSON (toJSON), decode)
import Data.Aeson.Encode.Pretty
import Data.ByteString.Lazy.Char8 qualified as BS
import Data.List (foldl')
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text (unpack)
import System.Environment (getArgs)
import Types

{- | Tests textual kore parser with given arguments and reports
   internalisation results.

   * Files given as arguments are parsed and internalised.  When a
   * directory is given as an argument, it is (recursively) searched
   * for files named "*.kore", which are parsed and internalised.
-}
main :: IO ()
main =
    getArgs >>= \case
        ["tree", file] -> do
            nested <- foldl' (foldl' toNested) (Nested mempty) . map decode . BS.lines <$> BS.readFile file
            BS.putStrLn $ encodePretty' defConfig{confIndent = Spaces 2} $ toJSON nested
        "aborts" : files -> do
            let countContexts m f = foldl' (foldl' countAborts) m . map decode . BS.lines <$> BS.readFile f
            (counts, rIdTorLoc) <- foldM countContexts mempty files
            forM_ (Map.toList counts) $ \(k, v) ->
                putStrLn $ unpack k <> " | " <> unpack (fromMaybe "-" $ Map.lookup k rIdTorLoc) <> " | " <> show v
        _ -> error "invalid option"
