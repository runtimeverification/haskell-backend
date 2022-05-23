{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- Added for outputFileName

module Main (main) where

import Kore.JsonRpc (runServer)
import Prelude.Kore

main :: IO ()
main = runServer
