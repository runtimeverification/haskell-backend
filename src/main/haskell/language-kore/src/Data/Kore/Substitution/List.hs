module Data.Kore.Substitution.List where

import qualified Data.Kore.Substitution.Class as C
import           Data.Maybe

newtype Substitution v t = Substitution { getSubstitution :: [(v,t)] }

instance C.Substitution Substitution where
    lookup v (Substitution l) = Prelude.lookup v l
    fromList = Substitution
    toList = getSubstitution
