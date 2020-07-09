{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

{-# OPTIONS_GHC -fno-prof-auto #-}

module Kore.Prof
    ( MonadProf (..)
    ) where

import Prelude.Kore hiding
    ( traceEventIO
    )

import Control.Monad.Catch
    ( bracket_
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Debug.Trace.Text
    ( traceEventIO
    )

class MonadProf monad where
    {- | Attribute an action to a particular name for profiling.
     -}
    traceProf
        :: Text  -- ^ name for profiling
        -> monad a  -- ^ action
        -> monad a

instance MonadProf IO where
    traceProf name =
        bracket_ open close
      where
        open = traceEventIO (Text.cons 'O' name)
        close = traceEventIO (Text.cons 'C' name)
