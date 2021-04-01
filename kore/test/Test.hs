{-# LANGUAGE Strict #-}
module Main (main) where

import qualified Driver
import Prelude.Kore
import qualified System.Environment as Environment

main :: IO ()
main = do
    -- Set TERM=dumb so that the --hide-successes option works correctly.
    Environment.setEnv "TERM" "dumb"
    Driver.main
