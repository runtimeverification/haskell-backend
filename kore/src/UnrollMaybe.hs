{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module UnrollMaybe (
    unrollMaybe,
) where

import Control.Lens ((??))
import Prelude.Kore

unrollMaybe :: Maybe (a -> b -> c) -> a -> b -> Maybe c
unrollMaybe = curry . (??) . fmap uncurry
