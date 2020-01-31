{- |
Copyright : (c) 2020 Runtime Verification
License   : NCSA

 -}

module Prelude.Kore
    ( module Prelude
    , isJust
    , isNothing
    , fromMaybe
    , Filterable (..)
    , headMay
    , HasCallStack
    , (&)
    ) where

-- TODO (thomas.tuegel): Give an explicit export list so that the generated
-- documentation is complete.

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
    ( filter
    , log
    )
