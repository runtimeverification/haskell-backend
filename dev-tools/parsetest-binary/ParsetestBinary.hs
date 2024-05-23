{- | Stand-alone parser executable for testing and profiling

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import Booster.Pattern.Base
import Booster.Pattern.Binary
import Booster.Syntax.ParsedKore

import Data.Binary.Get
import Data.ByteString.Lazy.Char8 qualified as BL
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text qualified as Text
import System.Environment (getArgs)

-- | Tests binary format parser with given file
main :: IO ()
main = do
    [binFile] <- getArgs
    print =<< test Nothing binFile

test :: Maybe (FilePath, Text.Text) -> FilePath -> IO Term
test (Just (definitionFile, mainModuleName)) f = do
    definitionMap <-
        either (error . show) id
            <$> loadDefinition [] definitionFile
    let internalModule =
            fromMaybe (error $ Text.unpack mainModuleName <> ": No such module") $
                Map.lookup mainModuleName definitionMap
    runGet (decodeTerm internalModule) <$> BL.readFile f
test Nothing f =
    runGet (decodeTerm' Nothing) <$> BL.readFile f
