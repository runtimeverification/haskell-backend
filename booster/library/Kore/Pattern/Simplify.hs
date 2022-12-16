{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Simplify (
    simplifyPredicate,
    splitBoolPredicates,
) where

import Kore.LLVM (simplifyBool)
import Kore.Pattern.Base
import Kore.Pattern.Util (isConcrete, sortOfTerm)
import System.Posix.DynamicLinker qualified as Linker

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

simplifyPredicate :: Maybe Linker.DL -> Predicate -> Predicate
simplifyPredicate dl = \case
    AndPredicate l r -> case (simplifyPredicate dl l, simplifyPredicate dl r) of
        (Bottom, _) -> Bottom
        (_, Bottom) -> Bottom
        (Top, r') -> r'
        (l', Top) -> l'
        (l', r') -> AndPredicate l' r'
    Bottom -> Bottom
    p@(Ceil _) -> p
    p@(EqualsTerm l r) ->
        case (dl, sortOfTerm l == SortBool && isConcrete l && isConcrete r) of
            (Just dlib, True) ->
                if simplifyBool dlib l == simplifyBool dlib r
                    then Top
                    else Bottom
            _ -> p
    EqualsPredicate l r -> EqualsPredicate (simplifyPredicate dl l) (simplifyPredicate dl r)
    p@(Exists _ _) -> p
    p@(Forall _ _) -> p
    Iff l r -> Iff (simplifyPredicate dl l) (simplifyPredicate dl r)
    Implies l r -> Implies (simplifyPredicate dl l) (simplifyPredicate dl r)
    p@(In _ _) -> p
    Not p -> case simplifyPredicate dl p of
        Top -> Bottom
        Bottom -> Top
        p' -> p'
    Or l r -> Or (simplifyPredicate dl l) (simplifyPredicate dl r)
    Top -> Top
