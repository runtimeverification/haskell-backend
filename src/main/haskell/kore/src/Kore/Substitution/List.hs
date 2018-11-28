{-|
Module      : Kore.Substitution.List
Description : Defines an instance of 'SubstitutionClass' using a list of
              variable |-> pattern pairs.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Kore.Substitution.List
    ( Substitution
    , SubstitutionClass(..)
    , MapClass(..)
    , fromList
    , toList
    ) where

import Data.List
       ( nubBy )

import Data.Map.Class
import Kore.AST.Kore
import Kore.AST.Pure
import Kore.Substitution.Class
import Kore.Variables.Free

-- |A very simple substitution represented as a list of pairs
newtype Substitution var pat = Substitution { getSubstitution :: [(var, pat)] }

instance
    ( Foldable dom
    , Functor dom
    , OrdMetaOrObject var
    , MetaOrObject lvl
    ) => SubstitutionClass
        Substitution
        (Unified var)
        (PurePattern lvl dom var ann)
  where
    substitutionTermsFreeVars =
        foldMap (freeVariables . snd) . getSubstitution

instance
    ( Foldable dom
    , Functor dom
    , OrdMetaOrObject var
    ) => SubstitutionClass
        Substitution
        (Unified var)
        (KorePattern dom var ann)
  where
    substitutionTermsFreeVars =
        foldMap (freeVariables . snd) . getSubstitution

instance Eq v => MapClass Substitution v t where
    isEmpty = null . getSubstitution
    empty = Substitution []
    lookup v (Substitution l) = Prelude.lookup v l
    delete v = Substitution . filter ((v /=) . fst) . getSubstitution
    insert v t  =
        Substitution . ((v,t) :) . filter ((v /=) . fst) . getSubstitution

fromList :: Eq k => [(k,v)] -> Substitution k v
fromList = Substitution . nubBy (\x y -> fst x == fst y)

toList :: Substitution k v -> [(k,v)]
toList = getSubstitution
