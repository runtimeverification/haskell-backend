module Main (main) where

import Prelude.Kore

import qualified System.Environment as Environment

import qualified Driver

main :: IO ()
main = do
    -- Set TERM=dumb so that the --hide-successes option works correctly.
    Environment.setEnv "TERM" "dumb"
    Driver.main
