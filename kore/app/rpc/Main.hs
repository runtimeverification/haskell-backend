{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- Added for outputFileName

module Main (main) where

import Prelude.Kore

import Kore.JsonRpc (runServer)

main :: IO ()
main = runServer