module Main where

-- import Data.ByteString.Char8 qualified as BS
import Data.Bifunctor as B
import Data.List.Extra
import Data.Map qualified as Map
import Data.Ord
import Text.Printf

main =
    getContents
        >>= mapM_ (uncurry (printf "| %s | %-3d|\n"))
            . sortOn (Down . snd)
            . Map.toList
            . Map.fromListWith (+)
            . map (,1 :: Int)
            . lines
