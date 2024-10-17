{- |
Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause

Function to manipulate @'Substitution'@s and convert to/from @'Predicate'@s

This module is intended to be imported qualified.
-}
module Booster.Pattern.Substitution (
    mkEq,
    destructEq,
    asEquations,
    partitionPredicates,
    compose,
    substituteInPredicate,
    substituteInTerm,
) where

import Data.Bifunctor (bimap)
import Data.Coerce (coerce)
import Data.List (partition)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe, isJust, mapMaybe)
import Data.Set qualified as Set

import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Util (sortOfTerm)

compose :: Substitution -> Substitution -> Substitution
compose newSubst oldSubst =
    let substitutedOldSubst = Map.map (substituteInTerm newSubst) oldSubst
     in (newSubst `Map.union` substitutedOldSubst) -- new bindings take priority

-- | Build an equality predicate form a variable assignment
mkEq :: Variable -> Term -> Predicate
mkEq x t = Predicate $ case sortOfTerm t of
    SortInt -> EqualsInt (Var x) t
    SortBool -> EqualsBool (Var x) t
    otherSort -> EqualsK (KSeq otherSort (Var x)) (KSeq otherSort t)

{- | Pattern match on an equality predicate and try extracting a variable assignment.
     This is a partial inverse of @'mkEq'@
-}
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

substituteInTerm :: Substitution -> Term -> Term
substituteInTerm substitution = goSubst
  where
    targetSet = Map.keysSet substitution
    goSubst t
        | Set.null (targetSet `Set.intersection` (getAttributes t).variables) = t
        | otherwise = case t of
            Var v -> fromMaybe t (Map.lookup v substitution)
            DomainValue{} -> t
            SymbolApplication sym sorts args ->
                SymbolApplication sym sorts $ map goSubst args
            AndTerm t1 t2 -> AndTerm (goSubst t1) (goSubst t2)
            Injection ss s sub -> Injection ss s (goSubst sub)
            KMap attrs keyVals rest -> KMap attrs (bimap goSubst goSubst <$> keyVals) (goSubst <$> rest)
            KList def heads rest ->
                KList def (map goSubst heads) (bimap goSubst (map goSubst) <$> rest)
            KSet def elements rest ->
                KSet def (map goSubst elements) (goSubst <$> rest)

substituteInPredicate :: Substitution -> Predicate -> Predicate
substituteInPredicate substitution = coerce . substituteInTerm substitution . coerce
