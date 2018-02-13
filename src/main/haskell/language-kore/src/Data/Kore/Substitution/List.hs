{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.List where

import qualified Data.Kore.Substitution.Class as C

newtype Substitution v t = Substitution { getSubstitution :: [(v,t)] }

instance Eq v => C.Substitution (Substitution v t) v t where
    isEmpty = null . getSubstitution
    lookup v (Substitution l) = Prelude.lookup v l
    fromList = Substitution
    toList = getSubstitution
    removeBinding v = Substitution . filter ((v /=) . fst) . getSubstitution
    addBinding v t  =
        Substitution . ((v,t) :) . filter ((v /=) . fst) . getSubstitution
