{-# LANGUAGE PatternSynonyms #-}

{- |
Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause
-}
module Booster.Pattern.Bool (
    foldAndBool,
    isBottom,
    negateBool,
    splitBoolPredicates,
    splitAndBools,
    -- patterns
    pattern TrueBool,
    pattern FalseBool,
    pattern NotBool,
    pattern AndBool,
    pattern EqualsInt,
    pattern EqualsBool,
    pattern NEqualsInt,
    pattern EqualsK,
    pattern NEqualsK,
    pattern SetIn,
) where

import Data.ByteString.Char8 (ByteString)
import Data.Text (Text)

import Booster.Definition.Attributes.Base (
    SMTType (SMTHook),
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
    pattern SortKItem,
    pattern SortSet,
    pattern SymbolApplication,
 )
import Booster.Pattern.Util (isConcrete)
import Booster.SMT.Base (SExpr (Atom), SMTId (..))

pattern TotalFunctionWithSMT :: ByteString -> SymbolAttributes
pattern TotalFunctionWithSMT hook =
    SymbolAttributes
        TotalFunction
        IsNotIdem
        IsNotAssoc
        IsNotMacroOrAlias
        CanBeEvaluated
        Nothing
        (Just (SMTHook (Atom (SMTId hook))))
        Nothing

pattern HookedFunctionWithSMT :: Text -> ByteString -> SymbolAttributes
pattern HookedFunctionWithSMT hook smt =
    SymbolAttributes
        TotalFunction
        IsNotIdem
        IsNotAssoc
        IsNotMacroOrAlias
        CanBeEvaluated
        Nothing
        (Just (SMTHook (Atom (SMTId smt))))
        (Just hook)

pattern AndBool :: Term -> Term -> Term
pattern AndBool l r =
    SymbolApplication
        ( Symbol
                "Lbl'Unds'andBool'Unds'"
                []
                [SortBool, SortBool]
                SortBool
                (TotalFunctionWithSMT "and")
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
                (TotalFunctionWithSMT "not")
            )
        []
        [t]

pattern EqualsInt, EqualsBool, NEqualsInt, EqualsK, NEqualsK, SetIn :: Term -> Term -> Term
pattern EqualsInt a b =
    SymbolApplication
        ( Symbol
                "Lbl'UndsEqlsEqls'Int'Unds'"
                []
                [SortInt, SortInt]
                SortBool
                (TotalFunctionWithSMT "=")
            )
        []
        [a, b]
pattern EqualsBool a b =
    SymbolApplication
        ( Symbol
                "Lbl'UndsEqlsEqls'Bool'Unds'"
                []
                [SortBool, SortBool]
                SortBool
                (TotalFunctionWithSMT "=")
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
                (TotalFunctionWithSMT "distinct")
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
                (HookedFunctionWithSMT "KEQUAL.eq" "=")
            )
        []
        [a, b]
pattern SetIn a b =
    SymbolApplication
        ( Symbol
                "LblSet'Coln'in"
                []
                [SortKItem, SortSet]
                SortBool
                ( SymbolAttributes
                        TotalFunction
                        IsNotIdem
                        IsNotAssoc
                        IsNotMacroOrAlias
                        CanBeEvaluated
                        Nothing
                        Nothing
                        Nothing
                    )
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
                (HookedFunctionWithSMT "KEQUAL.ne" "distinct")
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
        _other -> [p]

{- | Break apart a predicate composed of top-level Y1 andBool ... Yn
(not considering whether any of the subterms is concrete).
-}
splitAndBools :: Predicate -> [Predicate]
splitAndBools p@(Predicate t)
    | AndBool l r <- t = concatMap (splitAndBools . Predicate) [l, r]
    | otherwise = [p]
