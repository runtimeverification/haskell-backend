{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause
-}
module Booster.Pattern.Bool (
    -- export everything, modules above can re-export only type names
    module Booster.Pattern.Bool,
) where

import Booster.Definition.Attributes.Base (
    SymbolAttributes (SymbolAttributes),
    SymbolType (TotalFunction),
    pattern CanBeEvaluated,
    pattern IsNotAssoc,
    pattern IsNotIdem,
    pattern IsNotMacroOrAlias,
 )
import Booster.Pattern.Base (
    Pattern,
    Predicate (..),
    Symbol (Symbol),
    Term,
    constraints,
    pattern DomainValue,
    pattern SortBool,
    pattern SortInt,
    pattern SortK,
    pattern SymbolApplication,
 )
import Booster.Pattern.Util (isConcrete)

pattern AndBool :: Term -> Term -> Term
pattern AndBool l r =
    SymbolApplication
        ( Symbol
                "Lbl'Unds'andBool'Unds'"
                []
                [SortBool, SortBool]
                SortBool
                (SymbolAttributes TotalFunction IsNotIdem IsNotAssoc IsNotMacroOrAlias CanBeEvaluated Nothing)
            )
        []
        [l, r]

pattern NotBool :: Term -> Term
pattern NotBool t =
    SymbolApplication
        ( Symbol
                "LblnotBool'Unds'"
                []
                [SortBool]
                SortBool
                (SymbolAttributes TotalFunction IsNotIdem IsNotAssoc IsNotMacroOrAlias CanBeEvaluated Nothing)
            )
        []
        [t]

pattern EqualsInt, NEqualsInt, EqualsK, NEqualsK :: Term -> Term -> Term
pattern EqualsInt a b =
    SymbolApplication
        ( Symbol
                "Lbl'UndsEqlsEqls'Int'Unds'"
                []
                [SortInt, SortInt]
                SortBool
                (SymbolAttributes TotalFunction IsNotIdem IsNotAssoc IsNotMacroOrAlias CanBeEvaluated Nothing)
            )
        []
        [a, b]
pattern NEqualsInt a b =
    SymbolApplication
        ( Symbol
                "Lbl'UndsEqlsSlshEqls'Int'Unds'"
                []
                [SortInt, SortInt]
                SortBool
                (SymbolAttributes TotalFunction IsNotIdem IsNotAssoc IsNotMacroOrAlias CanBeEvaluated Nothing)
            )
        []
        [a, b]
pattern EqualsK a b =
    SymbolApplication
        ( Symbol
                "Lbl'UndsEqlsEqls'K'Unds'"
                []
                [SortK, SortK]
                SortBool
                (SymbolAttributes TotalFunction IsNotIdem IsNotAssoc IsNotMacroOrAlias CanBeEvaluated Nothing)
            )
        []
        [a, b]
pattern NEqualsK a b =
    SymbolApplication
        ( Symbol
                "Lbl'UndsEqlsSlshEqls'K'Unds'"
                []
                [SortK, SortK]
                SortBool
                (SymbolAttributes TotalFunction IsNotIdem IsNotAssoc IsNotMacroOrAlias CanBeEvaluated Nothing)
            )
        []
        [a, b]

pattern TrueBool, FalseBool :: Term
pattern TrueBool = DomainValue SortBool "true"
pattern FalseBool = DomainValue SortBool "false"

negateBool :: Term -> Term
negateBool TrueBool = FalseBool
negateBool FalseBool = TrueBool
negateBool x = NotBool x

foldAndBool :: [Term] -> Term
foldAndBool [] = TrueBool
foldAndBool [x] = x
foldAndBool (FalseBool : _) = FalseBool
foldAndBool (TrueBool : xs) = foldAndBool xs
foldAndBool (x : xs) = AndBool x $ foldAndBool xs

isBottom :: Pattern -> Bool
isBottom = (Predicate FalseBool `elem`) . constraints

{- | We want to break apart predicates of type `Y1 andBool ... Yn` apart, in case some of the `Y`s are abstract
which prevents the original expression from being fed to the LLVM simplifyBool function
-}
splitBoolPredicates :: Predicate -> [Predicate]
splitBoolPredicates p@(Predicate t)
    | isConcrete t = [p]
    | otherwise = case t of
        AndBool l r -> concatMap (splitBoolPredicates . Predicate) [l, r]
        other -> [Predicate other]
