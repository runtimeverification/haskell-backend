{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.List ( Substitution
                                   , SubstitutionClass(..)
                                   , MapClass(..)
                                   ) where

import           Data.List                       (nubBy)

import           Data.Kore.Substitution.Class
import           Data.Kore.Substitution.MapClass
import           Data.Kore.Variables.Free

-- |A very simple substitution represented as a list of pairs
newtype Substitution v t = Substitution { getSubstitution :: [(v,t)] }

instance (Ord v, TermWithVariablesClass t v)
    => SubstitutionClass (Substitution v t) v t where
    removeBinding v = Substitution . filter ((v /=) . fst) . getSubstitution
    addBinding v t  =
        Substitution . ((v,t) :) . filter ((v /=) . fst) . getSubstitution
    getFreeVars = foldMap (freeVariables . snd) . getSubstitution

instance MapClass (Substitution v t) v t where
    isEmpty = null . getSubstitution
    lookup v (Substitution l) = Prelude.lookup v l
    fromList = Substitution . nubBy (\x y -> fst x == fst y)
    toList = getSubstitution
