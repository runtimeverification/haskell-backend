{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Simplify (
    simplifyPredicate,
    splitBoolPredicates,
    simplifyConcrete,
) where

import Kore.Definition.Base
import Kore.LLVM (simplifyBool, simplifyTerm)
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

{- | traverses a term top-down, using a given LLVM dy.lib to simplify
 the concrete parts (leaving variables alone)
-}
simplifyConcrete :: Maybe Linker.DL -> KoreDefinition -> Term -> Term
simplifyConcrete Nothing _ trm = trm
simplifyConcrete (Just dl) def trm = recurse trm
  where
    recurse :: Term -> Term
    -- recursion scheme for this?
    --     cata $ \case does not work here, would need helpers for TermF not Term
    --         t | isConcreteF t -> simplifyTerm dl def t (sortOfTerm t)
    --         other -> embed other
    recurse = \case
        var@Var{} ->
            var -- nothing to do
        dv@DomainValue{} ->
            dv -- nothing to do
        t
            | isConcrete t ->
                -- FIXME repeats bottom-up traversal in isConcrete (needs cache)
                simplifyTerm dl def t (sortOfTerm t)
        AndTerm t1 t2 ->
            AndTerm (recurse t1) (recurse t2)
        SymbolApplication sym sorts args ->
            SymbolApplication sym sorts (map recurse args)

-- FIXME recursions repeat runLLVMwithDL (no sharing). This is
--  a more general problem with runLLVMwithDL, the library
--  should be fixed for the entire run but its functions are
--  reconstructed on every call
