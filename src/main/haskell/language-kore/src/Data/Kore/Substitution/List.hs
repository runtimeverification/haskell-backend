{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.List (Substitution, SubstitutionClass(..)) where

import           Data.List                    (nubBy)

import           Data.Kore.Substitution.Class

newtype Substitution v t = Substitution { getSubstitution :: [(v,t)] }

instance Eq v => SubstitutionClass (Substitution v t) v t where
    isEmpty = null . getSubstitution
    lookup v (Substitution l) = Prelude.lookup v l
    fromList = Substitution . nubBy (\x y -> fst x == fst y)
    toList = getSubstitution
    removeBinding v = Substitution . filter ((v /=) . fst) . getSubstitution
    addBinding v t  =
        Substitution . ((v,t) :) . filter ((v /=) . fst) . getSubstitution
