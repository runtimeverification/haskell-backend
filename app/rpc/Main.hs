{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Main (main) where

import Kore.JsonRpc (runServer)
import Prelude.Kore

main :: IO ()
main = runServer 31337
