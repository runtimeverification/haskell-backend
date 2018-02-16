{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.List ( Substitution
                                   , SubstitutionClass(..)
                                   , fromList
                                   , toList
                                   ) where

import           Data.List                    (nubBy)

import           Data.Kore.Substitution.Class
import           Data.Kore.Variables.Free

newtype Substitution v t = Substitution { getSubstitution :: [(v,t)] }

instance (Ord v, TermWithVariablesClass t v)
    => SubstitutionClass (Substitution v t) v t where
    isEmpty = null . getSubstitution
    lookup v (Substitution l) = Prelude.lookup v l
    removeBinding v = Substitution . filter ((v /=) . fst) . getSubstitution
    addBinding v t  =
        Substitution . ((v,t) :) . filter ((v /=) . fst) . getSubstitution
    getFreeVars = foldMap (freeVariables . snd) . getSubstitution

fromList :: Eq v => [(v,t)] -> Substitution v t
fromList = Substitution . nubBy (\x y -> fst x == fst y)

toList :: Substitution v t -> [(v,t)]
toList = getSubstitution
