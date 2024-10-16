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
    mkEq,
    destructEq,
    asEquations,
    partitionPredicates,
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
import Data.List (partition)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, mapMaybe)

import Booster.Definition.Attributes.Base (
    FunctionType (..),
    SMTType (SMTHook),
    SymbolAttributes (SymbolAttributes),
    SymbolType (Function),
    pattern CanBeEvaluated,
    pattern IsNotAssoc,
    pattern IsNotIdem,
    pattern IsNotMacroOrAlias,
 )
import Booster.Pattern.Base (
    Pattern (..),
    Predicate (..),
    Symbol (Symbol),
    Term,
    Variable,
    pattern DomainValue,
    pattern KSeq,
    pattern SortBool,
    pattern SortInt,
    pattern SortK,
    pattern SortKItem,
    pattern SortSet,
    pattern SymbolApplication,
    pattern Var,
 )
import Booster.Pattern.Util (isConcrete, sortOfTerm)
import Booster.SMT.Base (SExpr (Atom), SMTId (..))

pattern HookedTotalFunction :: ByteString -> SymbolAttributes
pattern HookedTotalFunction hook =
    SymbolAttributes
        (Function Total)
        IsNotIdem
        IsNotAssoc
        IsNotMacroOrAlias
        CanBeEvaluated
        Nothing
        Nothing
        (Just hook)

pattern HookedTotalFunctionWithSMT :: ByteString -> ByteString -> SymbolAttributes
pattern HookedTotalFunctionWithSMT hook smt =
    SymbolAttributes
        (Function Total)
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
                (HookedTotalFunctionWithSMT "BOOL.and" "and")
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
                (HookedTotalFunctionWithSMT "BOOL.not" "not")
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
                (HookedTotalFunctionWithSMT "INT.eq" "=")
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
                (HookedTotalFunctionWithSMT "BOOL.eq" "=")
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
                (HookedTotalFunctionWithSMT "INT.ne" "distinct")
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
                (HookedTotalFunctionWithSMT "KEQUAL.eq" "=")
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
                (HookedTotalFunction "SET.in")
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
                (HookedTotalFunctionWithSMT "KEQUAL.ne" "distinct")
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

mkEq :: Variable -> Term -> Predicate
mkEq x t = Predicate $ case sortOfTerm t of
    SortInt -> EqualsInt (Var x) t
    SortBool -> EqualsBool (Var x) t
    otherSort -> EqualsK (KSeq otherSort (Var x)) (KSeq otherSort t)

-- | Pattern match on an equality predicate and try extracting a variable assignment
destructEq :: Predicate -> Maybe (Variable, Term)
destructEq = \case
    Predicate (EqualsInt (Var x) t) -> Just (x, t)
    Predicate (EqualsBool (Var x) t) -> Just (x, t)
    Predicate
        (EqualsK (KSeq _lhsSort (Var x)) (KSeq _rhsSort t)) -> Just (x, t)
    _ -> Nothing

-- | turns a substitution into a list of equations
asEquations :: Map Variable Term -> [Predicate]
asEquations = map (uncurry mkEq) . Map.assocs

-- | Extract substitution items from a list of generic predicates. Return empty substitution if none are found
partitionPredicates :: [Predicate] -> (Map Variable Term, [Predicate])
partitionPredicates ps =
    let (substItems, normalPreds) = partition (isJust . destructEq) ps
     in (Map.fromList . mapMaybe destructEq $ substItems, normalPreds)
