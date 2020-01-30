{- |
Copyright : (c) 2020 Runtime Verification
License   : NCSA

 -}

module Prelude.Kore
    ( module Prelude
    , HasCallStack
    , (&)
    ) where

-- TODO (thomas.tuegel): Give an explicit export list so that the generated
-- documentation is complete.

import Data.Function
    ( (&)
    )
import GHC.Stack
    ( HasCallStack
    )
import Prelude hiding
    ( log
    )
