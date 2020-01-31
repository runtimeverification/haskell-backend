{- |
Copyright : (c) 2020 Runtime Verification
License   : NCSA

 -}

module Prelude.Kore
    ( module Prelude
    , isJust
    , isNothing
    , fromMaybe
    ) where

-- TODO (thomas.tuegel): Give an explicit export list so that the generated
-- documentation is complete.

import Data.Maybe
    ( fromMaybe
    , isJust
    , isNothing
    )
import Prelude hiding
    ( log
    )
