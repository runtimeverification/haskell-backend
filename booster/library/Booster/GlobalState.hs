module Booster.GlobalState (
    EquationOptions (..),
    globalEquationOptions,
    readGlobalEquationOptions,
    writeGlobalEquationOptions,
) where

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

import Booster.Util (Bound (..))

data EquationOptions = EquationOptions
    { maxIterations :: Bound "Iterations"
    , maxRecursion :: Bound "Recursion"
    }
    deriving stock (Show, Eq)

{-# NOINLINE globalEquationOptions #-}
globalEquationOptions :: IORef EquationOptions
globalEquationOptions =
    unsafePerformIO . newIORef $
        EquationOptions{maxIterations = 100, maxRecursion = 5}

readGlobalEquationOptions :: IO EquationOptions
readGlobalEquationOptions = readIORef globalEquationOptions

writeGlobalEquationOptions :: EquationOptions -> IO ()
writeGlobalEquationOptions = atomicWriteIORef globalEquationOptions
