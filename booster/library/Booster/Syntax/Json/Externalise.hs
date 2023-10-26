{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Syntax.Json.Externalise (
    externalisePattern,
    externalisePredicate,
    externaliseSort,
    externaliseTerm,
) where

import Data.Foldable ()
import Data.List (partition)
import Data.Set qualified as Set
import Data.Text.Encoding qualified as Text

import Booster.Pattern.Base (externaliseKmapUnsafe)
import Booster.Pattern.Base qualified as Internal
import Booster.Pattern.Util (sortOfTerm)
import Kore.Syntax.Json.Types qualified as Syntax

{- | Converts an internal pattern to a triple of term, predicate and substitution in
 external format. The predicate and substitution are 'And'ed to avoid leaking
 Json format internals to the caller.
-}
externalisePattern ::
    Internal.Pattern ->
    (Syntax.KorePattern, Maybe Syntax.KorePattern, Maybe Syntax.KorePattern)
externalisePattern Internal.Pattern{term = term, constraints} =
    -- need a sort for the predicates in external format
    let sort = externaliseSort $ sortOfTerm term
        (substitutionItems, predicateItems) =
            partition isSubstitutionItem $ Set.toList constraints
        substitution =
            if null substitutionItems
                then Nothing
                else Just . multiAnd sort . map (externalisePredicate sort) $ substitutionItems
        predicate =
            if null predicateItems
                then Nothing
                else Just . multiAnd sort . map (externalisePredicate sort) $ predicateItems
     in (externaliseTerm term, predicate, substitution)
  where
    multiAnd :: Syntax.Sort -> [Syntax.KorePattern] -> Syntax.KorePattern
    multiAnd _ [] = error "multiAnd: empty"
    multiAnd _ [p] = p
    multiAnd sort ps = Syntax.KJAnd sort ps

    isSubstitutionItem :: Internal.Predicate -> Bool
    isSubstitutionItem (Internal.EqualsTerm lhs _rhs) = isVariable lhs
    isSubstitutionItem (Internal.AndPredicate lhs rhs) = isSubstitutionItem lhs && isSubstitutionItem rhs
    isSubstitutionItem _ = False

    isVariable :: Internal.Term -> Bool
    isVariable (Internal.Var _) = True
    isVariable _ = False

-- TODO: should KorePattern be the only type with an actual Unparse instance?
externaliseTerm :: Internal.Term -> Syntax.KorePattern
externaliseTerm = \case
    Internal.AndTerm first' second' ->
        Syntax.KJAnd
            (externaliseSort $ sortOfTerm second')
            [ externaliseTerm first'
            , externaliseTerm second'
            ]
    Internal.SymbolApplication symbol sorts args ->
        Syntax.KJApp
            (symbolNameToId symbol.name)
            (map externaliseSort sorts)
            (map externaliseTerm args)
    Internal.DomainValue sort bs ->
        Syntax.KJDV (externaliseSort sort) $ Text.decodeLatin1 bs
    Internal.Var Internal.Variable{variableSort = iSort, variableName = iName} ->
        Syntax.KJEVar (varNameToId iName) (externaliseSort iSort)
    Internal.Injection source target trm ->
        Syntax.KJApp
            (symbolNameToId Internal.injectionSymbol.name)
            (map externaliseSort [source, target])
            [externaliseTerm trm]
    Internal.KMap def keyVals rest -> externaliseTerm $ externaliseKmapUnsafe def keyVals rest
    Internal.KList def heads rest ->
        externaliseTerm $ Internal.externaliseKList def heads rest
    Internal.KSet def heads rest ->
        externaliseTerm $ Internal.externaliseKSet def heads rest

externalisePredicate :: Syntax.Sort -> Internal.Predicate -> Syntax.KorePattern
externalisePredicate sort =
    let recursion = externalisePredicate sort
     in \case
            Internal.AndPredicate p1 p2 ->
                Syntax.KJAnd{sort, patterns = [recursion p1, recursion p2]}
            Internal.Bottom ->
                Syntax.KJBottom{sort}
            Internal.Ceil term ->
                Syntax.KJCeil
                    { argSort = externaliseSort $ sortOfTerm term
                    , sort
                    , arg = externaliseTerm term
                    }
            Internal.EqualsTerm t1 t2 ->
                Syntax.KJEquals
                    { argSort = externaliseSort $ sortOfTerm t1
                    , sort
                    , first = externaliseTerm t1
                    , second = externaliseTerm t2
                    }
            Internal.EqualsPredicate p1 p2 ->
                Syntax.KJEquals{argSort = sort, sort, first = recursion p1, second = recursion p2}
            Internal.Exists var p1 ->
                Syntax.KJExists
                    { sort
                    , var = varNameToId var.variableName
                    , varSort = externaliseSort var.variableSort
                    , arg = recursion p1
                    }
            Internal.Forall var p1 ->
                Syntax.KJForall
                    { sort
                    , var = varNameToId var.variableName
                    , varSort = externaliseSort var.variableSort
                    , arg = recursion p1
                    }
            Internal.Iff p1 p2 ->
                Syntax.KJIff{sort, first = recursion p1, second = recursion p2}
            Internal.Implies p1 p2 ->
                Syntax.KJImplies{sort, first = recursion p1, second = recursion p2}
            Internal.In t1 t2 ->
                Syntax.KJIn
                    { argSort = externaliseSort $ sortOfTerm t1
                    , sort
                    , first = externaliseTerm t1
                    , second = externaliseTerm t2
                    }
            Internal.Not p1 ->
                Syntax.KJNot{sort, arg = recursion p1}
            Internal.Or p1 p2 ->
                Syntax.KJOr{sort, patterns = [recursion p1, recursion p2]}
            Internal.Top ->
                Syntax.KJTop{sort}

varNameToId :: Internal.VarName -> Syntax.Id
varNameToId = Syntax.Id . Text.decodeLatin1

sortNameToId :: Internal.SortName -> Syntax.Id
sortNameToId = Syntax.Id . Text.decodeLatin1

symbolNameToId :: Internal.SymbolName -> Syntax.Id
symbolNameToId = Syntax.Id . Text.decodeLatin1

-- | converts an internal sort to an external one
externaliseSort :: Internal.Sort -> Syntax.Sort
externaliseSort (Internal.SortApp name args) =
    Syntax.SortApp (sortNameToId name) (map externaliseSort args)
externaliseSort (Internal.SortVar name) =
    Syntax.SortVar $ sortNameToId name
