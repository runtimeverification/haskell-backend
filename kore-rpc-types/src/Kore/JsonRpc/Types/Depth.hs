module Kore.JsonRpc.Types.Depth (module Kore.JsonRpc.Types.Depth) where

import Data.Aeson.Types (FromJSON (..), ToJSON (..))
import Numeric.Natural

newtype Depth = Depth {getNat :: Natural}
    deriving stock (Show, Eq)
    deriving newtype (FromJSON, ToJSON, Num)
