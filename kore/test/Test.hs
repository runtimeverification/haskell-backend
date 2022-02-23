module Main (main) where

import Driver qualified
import Prelude.Kore
import System.Environment qualified as Environment

main :: IO ()
main = do
    -- Set TERM=dumb so that the --hide-successes option works correctly.
    Environment.setEnv "TERM" "dumb"
    Driver.main
