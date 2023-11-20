{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Simplify (
    splitBoolPredicates,
) where

import Booster.Pattern.Base
import Booster.Pattern.Util (isConcrete)

{- | We want to break apart predicates of type `Y1 andBool ... Yn` apart, in case some of the `Y`s are abstract
which prevents the original expression from being fed to the LLVM simplifyBool function
-}
splitBoolPredicates :: Predicate -> [Predicate]
splitBoolPredicates p@(Predicate t)
    | isConcrete t = [p]
    | otherwise = case t of
        AndBool ts -> concatMap (splitBoolPredicates . Predicate) ts
        other -> [Predicate other]
