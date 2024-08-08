module Kore.JsonRpc.Types.Depth (module Kore.JsonRpc.Types.Depth) where

import Data.Aeson.Types (FromJSON (..), ToJSON (..))
import Numeric.Natural
import Prettyprinter qualified as Pretty

newtype Depth = Depth {getNat :: Natural}
    deriving stock (Show, Eq)
    deriving newtype (FromJSON, ToJSON, Num, Pretty.Pretty)
