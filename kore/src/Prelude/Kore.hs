{- |
Copyright : (c) 2020 Runtime Verification
License   : NCSA

 -}

module Prelude.Kore
    ( module Prelude
    , module Debug.Trace
    -- * Ord
    , minMax
    -- * Functions
    , (&)
    , on
    -- * Maybe
    , isJust
    , isNothing
    , fromMaybe
    , headMay
    -- * Either
    , either
    , isLeft, isRight
    -- * Filterable
    , Filterable (..)
    -- * Errors
    , HasCallStack
    , assert
    -- * Applicative and Alternative
    , Applicative (..)
    , Alternative (..)
    , optional
    -- * From
    , module From
    -- * Comonad
    , module Control.Comonad
    -- * Hashable
    , Hashable (..)
    -- * Monad
    , Monad (..)
    , MonadPlus (..)
    , MonadIO (..)
    , MonadTrans (..)
    ) where

-- TODO (thomas.tuegel): Give an explicit export list so that the generated
-- documentation is complete.

import Control.Applicative
    ( Alternative (..)
    , Applicative (..)
    , optional
    )
import Control.Comonad
import Control.Error
    ( either
    , headMay
    , isLeft
    , isRight
    )
import Control.Exception
    ( assert
    )
import Control.Monad
    ( Monad (..)
    , MonadPlus (..)
    )
import Control.Monad.IO.Class
    ( MonadIO (..)
    )
import Control.Monad.Trans.Class
    ( MonadTrans (..)
    )
import Data.Function
    ( on
    , (&)
    )
import Data.Hashable
    ( Hashable (..)
    )
import Data.Maybe
    ( fromMaybe
    , isJust
    , isNothing
    )
import Data.Witherable
    ( Filterable (..)
    )
import Debug.Trace
import From
import GHC.Stack
    ( HasCallStack
    )
import Prelude hiding
    ( Applicative (..)
    , Monad (..)
    , either
    , filter
    , log
    )

{- | Simultaneously compute the (@min@, @max@) of two values.
 -}
minMax :: Ord a => a -> a -> (a, a)
minMax a b
  | a < b     = (a, b)
  | otherwise = (b, a)
