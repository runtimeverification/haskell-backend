{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Pattern.Util (
    applySubst,
    sortOfTerm,
    sortOfTermOrPredicate,
    sortOfPattern,
    retractPattern,
    substituteInTerm,
    substituteInPredicate,
    modifyVariables,
    modifyVariablesInT,
    modifyVariablesInP,
    modifyVarName,
    modifyVarNameConcreteness,
    freeVariables,
    isConstructorSymbol,
    isSortInjectionSymbol,
    isFunctionSymbol,
    isDefinedSymbol,
    checkSymbolIsAc,
    checkTermSymbols,
    isBottom,
    isConcrete,
    filterTermSymbols,
) where

import Data.Bifunctor (bimap, first)
import Data.ByteString (ByteString)
import Data.Coerce (coerce)
import Data.Functor.Foldable (Corecursive (embed), cata)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set qualified as Set

import Booster.Definition.Attributes.Base (
    Concreteness (..),
    Flag (..),
    KCollectionMetadata (..),
    KListDefinition (..),
    KMapDefinition (..),
    SymbolAttributes (..),
    SymbolType (..),
 )
import Booster.Pattern.Base

-- | Returns the sort of a term
sortOfTerm :: Term -> Sort
sortOfTerm (AndTerm _ child) = sortOfTerm child
sortOfTerm (SymbolApplication symbol sorts _) =
    applySubst (Map.fromList $ zip symbol.sortVars sorts) symbol.resultSort
sortOfTerm (DomainValue sort _) = sort
sortOfTerm (Var Variable{variableSort}) = variableSort
sortOfTerm (Injection _ sort _) = sort
sortOfTerm (KMap def _ _) = SortApp def.mapSortName []
sortOfTerm (KList def _ _) = SortApp def.listSortName []

applySubst :: Map VarName Sort -> Sort -> Sort
applySubst subst var@(SortVar n) =
    fromMaybe var $ Map.lookup n subst
applySubst subst (SortApp n args) =
    SortApp n $ map (applySubst subst) args

sortOfTermOrPredicate :: TermOrPredicate -> Maybe Sort
sortOfTermOrPredicate (TermAndPredicate Pattern{term}) = Just (sortOfTerm term)
sortOfTermOrPredicate (APredicate _) = Nothing

sortOfPattern :: Pattern -> Sort
sortOfPattern pat = sortOfTerm pat.term

retractPattern :: TermOrPredicate -> Maybe Pattern
retractPattern (TermAndPredicate patt) = Just patt
retractPattern _ = Nothing

substituteInTerm :: Map Variable Term -> Term -> Term
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

substituteInPredicate :: Map Variable Term -> Predicate -> Predicate
substituteInPredicate substitution = cata $ \case
    EqualsTermF t1 t2 ->
        EqualsTerm (substituteInTerm substitution t1) (substituteInTerm substitution t2)
    other -> embed other

modifyVariables :: (Variable -> Variable) -> Pattern -> Pattern
modifyVariables f p =
    Pattern
        { term = modifyVariablesInT f p.term
        , constraints = map (modifyVariablesInP f) p.constraints
        }

modifyVariablesInT :: (Variable -> Variable) -> Term -> Term
modifyVariablesInT f = cata $ \case
    VarF v -> Var (f v)
    other -> embed other

modifyVariablesInP :: (Variable -> Variable) -> Predicate -> Predicate
modifyVariablesInP f = cata $ \case
    EqualsTermF t1 t2 ->
        EqualsTerm (modifyVariablesInT f t1) (modifyVariablesInT f t2)
    InF t1 t2 ->
        In (modifyVariablesInT f t1) (modifyVariablesInT f t2)
    CeilF t ->
        Ceil (modifyVariablesInT f t)
    ExistsF v pr ->
        Exists (f v) (modifyVariablesInP f pr)
    ForallF v pr ->
        Forall (f v) (modifyVariablesInP f pr)
    other -> embed other

modifyVarName :: (VarName -> VarName) -> Variable -> Variable
modifyVarName f v = v{variableName = f v.variableName}

modifyVarNameConcreteness :: (ByteString -> ByteString) -> Concreteness -> Concreteness
modifyVarNameConcreteness f = \case
    SomeConstrained m -> SomeConstrained $ Map.mapKeys (first f) m
    other -> other

freeVariables :: Term -> Set Variable
freeVariables (Term attributes _) = attributes.variables

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
    coerce symbol.attributes.isAssoc || coerce symbol.attributes.isIdem

checkTermSymbols :: (Symbol -> Bool) -> Term -> Bool
checkTermSymbols check = cata $ \case
    SymbolApplicationF symbol _ ts -> check symbol && and ts
    other -> and other

filterTermSymbols :: (Symbol -> Bool) -> Term -> [Symbol]
filterTermSymbols check = cata $ \case
    SymbolApplicationF symbol _ ts
        | check symbol -> symbol : concat ts
        | otherwise -> concat ts
    AndTermF t1 t2 -> t1 <> t2
    DomainValueF _ _ -> []
    VarF _ -> []
    InjectionF _ _ t -> t
    KMapF def [] Nothing -> [unit | let unit = unitSymbol $ KMapMeta def, check unit]
    KMapF _ [] (Just t) -> t
    KMapF def kvs t ->
        let
            concatSym = concatSymbol $ KMapMeta def
            elementSym = kmapElementSymbol def
            unitSym = unitSymbol $ KMapMeta def
         in
            filter check [concatSym, elementSym, unitSym]
                <> concatMap (uncurry (<>)) kvs
                <> fromMaybe [] t
    KListF def heads Nothing ->
        let concatSym = concatSymbol $ KListMeta def
            elemSym = klistElementSymbol def
            unitSym = unitSymbol $ KListMeta def
         in if null heads
                then [unitSym | check unitSym]
                else filter check [concatSym, elemSym] <> concat heads
    KListF def heads (Just (mid, tails)) ->
        let concatSym = concatSymbol $ KListMeta def
            elemSym = klistElementSymbol def
            unitSym = unitSymbol $ KListMeta def
            ends = heads <> tails
         in mid
                <> if null ends
                    then []
                    else filter check [concatSym, elemSym, unitSym] <> concat ends

isBottom :: Pattern -> Bool
isBottom = (Bottom `elem`) . constraints
