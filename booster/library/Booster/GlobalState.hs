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
    , maxLocalSteps :: Bound "LocalSteps"
    {- ^ how many equations may be applied in place at a rewritten
    subterm (per chain of in-place rewrites) before falling back
    to restarting the traversal from the top (0, the default, is
    restart-only evaluation)
    -}
    }
    deriving stock (Show, Eq)

{-# NOINLINE globalEquationOptions #-}
globalEquationOptions :: IORef EquationOptions
globalEquationOptions =
    unsafePerformIO . newIORef $
        EquationOptions
            { maxIterations = 100
            , maxRecursion = 5
            , maxLocalSteps = 0
            }

readGlobalEquationOptions :: IO EquationOptions
readGlobalEquationOptions = readIORef globalEquationOptions

writeGlobalEquationOptions :: EquationOptions -> IO ()
writeGlobalEquationOptions = atomicWriteIORef globalEquationOptions
