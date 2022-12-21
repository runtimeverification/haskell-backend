{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Util (
    applySubst,
    sortOfTerm,
    sortOfTermOrPredicate,
    retractPattern,
    substituteInTerm,
    substituteInPredicate,
    modifyVariables,
    freeVariables,
    isConstructorSymbol,
    isSortInjectionSymbol,
    isFunctionSymbol,
    isDefinedSymbol,
    checkSymbolIsAc,
    checkTermSymbols,
    isBottom,
    isConcrete,
    decodeLabel,
) where

import Data.Foldable (fold)
import Data.Functor.Foldable (Corecursive (embed), cata)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Kore.Definition.Attributes.Base (SymbolAttributes (..), SymbolType (..))
import Kore.Pattern.Base

-- | Returns the sort of a term
sortOfTerm :: Term -> Sort
sortOfTerm (AndTerm _ child) = sortOfTerm child
sortOfTerm (SymbolApplication symbol sorts _) =
    applySubst (Map.fromList $ zip symbol.sortVars sorts) symbol.resultSort
sortOfTerm (DomainValue sort _) = sort
sortOfTerm (Var Variable{variableSort}) = variableSort

applySubst :: Map VarName Sort -> Sort -> Sort
applySubst subst var@(SortVar n) =
    fromMaybe var $ Map.lookup n subst
applySubst subst (SortApp n args) =
    SortApp n $ map (applySubst subst) args

sortOfTermOrPredicate :: TermOrPredicate -> Maybe Sort
sortOfTermOrPredicate (TermAndPredicate Pattern{term}) = Just (sortOfTerm term)
sortOfTermOrPredicate (APredicate _) = Nothing

retractPattern :: TermOrPredicate -> Maybe Pattern
retractPattern (TermAndPredicate patt) = Just patt
retractPattern _ = Nothing

substituteInTerm :: Map Variable Term -> Term -> Term
substituteInTerm substitution = cata $ \case
    VarF v -> fromMaybe (Var v) (Map.lookup v substitution)
    other -> embed other

substituteInPredicate :: Map Variable Term -> Predicate -> Predicate
substituteInPredicate substitution = cata $ \case
    EqualsTermF t1 t2 ->
        EqualsTerm (substituteInTerm substitution t1) (substituteInTerm substitution t2)
    other -> embed other

modifyVariables :: (VarName -> VarName) -> Pattern -> Pattern
modifyVariables f p =
    Pattern
        { term = modifyT p.term
        , constraints = map modifyP p.constraints
        }
  where
    modifyT :: Term -> Term
    modifyT = cata $ \case
        VarF v@Variable{variableName} ->
            Var v{variableName = f variableName}
        other -> embed other
    modifyP :: Predicate -> Predicate
    modifyP = cata $ \case
        EqualsTermF t1 t2 ->
            EqualsTerm (modifyT t1) (modifyT t2)
        other -> embed other

freeVariables :: Term -> Set Variable
freeVariables = cata $ \case
    VarF var -> Set.singleton var
    other -> fold other

-- | Don't use unless therm size is small
isConcrete :: Term -> Bool
isConcrete = Set.null . freeVariables

isConstructorSymbol :: Symbol -> Bool
isConstructorSymbol symbol =
    case symbol.attributes.symbolType of
        Constructor -> True
        _ -> False

isSortInjectionSymbol :: Symbol -> Bool
isSortInjectionSymbol symbol =
    case symbol.attributes.symbolType of
        SortInjection -> True
        _ -> False

isFunctionSymbol :: Symbol -> Bool
isFunctionSymbol symbol =
    case symbol.attributes.symbolType of
        TotalFunction -> True
        PartialFunction -> True
        _ -> False

isDefinedSymbol :: Symbol -> Bool
isDefinedSymbol symbol =
    case symbol.attributes.symbolType of
        Constructor -> True
        TotalFunction -> True
        SortInjection -> True
        PartialFunction -> False

checkSymbolIsAc :: Symbol -> Bool
checkSymbolIsAc symbol =
    symbol.attributes.isAssoc || symbol.attributes.isIdem

checkTermSymbols :: (Symbol -> Bool) -> Term -> Bool
checkTermSymbols check = cata $ \case
    SymbolApplicationF symbol _ ts -> check symbol && and ts
    other -> and other

isBottom :: Pattern -> Bool
isBottom = (Bottom `elem`) . constraints
