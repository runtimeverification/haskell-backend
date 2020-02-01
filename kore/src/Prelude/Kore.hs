{- |
Copyright : (c) 2020 Runtime Verification
License   : NCSA

 -}

module Prelude.Kore
    ( module Prelude
    -- * Functions
    , (&)
    -- * Maybe
    , isJust
    , isNothing
    , fromMaybe
    , headMay
    -- * Filterable
    , Filterable (..)
    -- * Errors
    , HasCallStack
    -- * Applicative and Alternative
    , Applicative (..)
    , Alternative (..)
    ) where

-- TODO (thomas.tuegel): Give an explicit export list so that the generated
-- documentation is complete.

import Control.Applicative
    ( Alternative (..)
    , Applicative (..)
    )
import Control.Error
    ( headMay
    )
import Data.Function
    ( (&)
    )
import Data.Maybe
    ( fromMaybe
    , isJust
    , isNothing
    )
import Data.Witherable
    ( Filterable (..)
    )
import GHC.Stack
    ( HasCallStack
    )
import Prelude hiding
    ( Applicative (..)
    , filter
    , log
    )
