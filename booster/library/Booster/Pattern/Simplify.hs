{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Simplify (
    splitBoolPredicates,
) where

import Booster.Pattern.Base
import Booster.Pattern.Util (isConcrete)

{- | We want to break apart predicates of type `X #Equals Y1 andBool ... Yn` into
`X #Equals Y1, ..., X #Equals  Yn` in the case when some of the `Y`s are abstract
and thus the whole original expression could not be fed to the LLVM simplifyBool function
-}
splitBoolPredicates :: Predicate -> [Predicate]
splitBoolPredicates = \case
    p@(EqualsTerm l r) | isConcrete l && isConcrete r -> [p]
    EqualsTerm (AndBool ls) r -> concatMap (splitBoolPredicates . flip EqualsTerm r) ls
    EqualsTerm l (AndBool rs) -> concatMap (splitBoolPredicates . EqualsTerm l) rs
    other -> [other]
