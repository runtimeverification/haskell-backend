{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Util (
    sortOfTerm,
    sortOfTermOrPredicate,
    retractPattern,
    substituteInTerm,
    substituteInPredicate,
    freeVariables,
) where

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set

import Kore.Pattern.Base

-- | Returns the sort of a term
sortOfTerm :: Term -> Sort
sortOfTerm (AndTerm sort _ _) = sort
sortOfTerm (SymbolApplication sort _ _ _) = sort
sortOfTerm (DomainValue sort _) = sort
sortOfTerm (Var Variable{variableSort}) = variableSort

sortOfTermOrPredicate :: TermOrPredicate -> Maybe Sort
sortOfTermOrPredicate (TermAndPredicate Pattern{term}) = Just (sortOfTerm term)
sortOfTermOrPredicate (APredicate _) = Nothing

retractPattern :: TermOrPredicate -> Maybe Pattern
retractPattern (TermAndPredicate patt) = Just patt
retractPattern _ = Nothing

substituteInTerm :: Map Variable Term -> Term -> Term
substituteInTerm substitution term =
    case term of
        AndTerm sort t1 t2 ->
            AndTerm sort (substituteInTerm substitution t1) (substituteInTerm substitution t2)
        SymbolApplication sort sorts symname sargs ->
            SymbolApplication sort sorts symname (substituteInTerm substitution <$> sargs)
        dv@(DomainValue _ _) -> dv
        v@(Var var) ->
            fromMaybe v (Map.lookup var substitution)

substituteInPredicate :: Map Variable Term -> Predicate -> Predicate
substituteInPredicate substitution predicate =
    case predicate of
        AndPredicate p1 p2 ->
            AndPredicate (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
        Bottom -> Bottom
        Ceil t -> Ceil (substituteInTerm substitution t)
        EqualsTerm sort t1 t2 ->
            EqualsTerm sort (substituteInTerm substitution t1) (substituteInTerm substitution t2)
        EqualsPredicate p1 p2 ->
            EqualsPredicate (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
        Exists v p ->
            Exists v (substituteInPredicate substitution p)
        Forall v p ->
            Forall v (substituteInPredicate substitution p)
        Iff p1 p2 ->
            Iff (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
        Implies p1 p2 ->
            Implies (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
        In sort t1 t2 ->
            In sort (substituteInTerm substitution t1) (substituteInTerm substitution t2)
        Not p ->
            Not (substituteInPredicate substitution p)
        Or p1 p2 ->
            Or (substituteInPredicate substitution p1) (substituteInPredicate substitution p2)
        Top -> Top

freeVariables :: Term -> Set Variable
freeVariables = \case
    AndTerm _ t1 t2 ->
        freeVariables t1 <> freeVariables t2
    SymbolApplication _sort _sorts _symname sargs ->
        Set.unions $ map freeVariables sargs
    DomainValue _ _ -> Set.empty
    Var var -> Set.singleton var
