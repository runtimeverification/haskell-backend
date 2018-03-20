{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Substitution.List ( Substitution
                                   , SubstitutionClass(..)
                                   , MapClass(..)
                                   , fromList
                                   , toList
                                   ) where

import           Data.List                         (nubBy)

import           Data.Kore.Datastructures.MapClass
import           Data.Kore.Substitution.Class
import           Data.Kore.Variables.Free

-- |A very simple substitution represented as a list of pairs
newtype Substitution v t = Substitution { getSubstitution :: [(v,t)] }

instance (Ord v, TermWithVariablesClass t v)
    => SubstitutionClass (Substitution v t) v t where
    substitutionTermsFreeVars = foldMap (freeVariables . snd) . getSubstitution

instance EmptyTestable (Substitution v t) where
    isEmpty = null . getSubstitution
    empty = Substitution []

instance Eq v => MapClass (Substitution v t) v t where
    lookup v (Substitution l) = Prelude.lookup v l
    delete v = Substitution . filter ((v /=) . fst) . getSubstitution
    insert v t  =
        Substitution . ((v,t) :) . filter ((v /=) . fst) . getSubstitution

fromList :: Eq k => [(k,v)] -> Substitution k v
fromList = Substitution . nubBy (\x y -> fst x == fst y)

toList :: Substitution k v -> [(k,v)]
toList = getSubstitution
