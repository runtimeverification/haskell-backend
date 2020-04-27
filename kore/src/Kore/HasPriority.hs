module Kore.HasPriority
    ( HasPriority (..)
    ) where

import Prelude.Kore

class HasPriority has where
    getPriority :: has -> Integer
