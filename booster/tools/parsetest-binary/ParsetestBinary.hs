{- | Stand-alone parser executable for testing and profiling

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Main (
    main,
) where

import System.Environment (getArgs)

import Booster.Pattern.Binary

{- | Tests textual kore parser with given arguments and reports
   internalisation results.

   * Files given as arguments are parsed and internalised.  When a
   * directory is given as an argument, it is (recursively) searched
   * for files named "*.kore", which are parsed and internalised.
-}
main :: IO ()
main = do
    [binFile] <- getArgs
    print =<< test Nothing binFile
