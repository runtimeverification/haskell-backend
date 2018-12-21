{-|
Module      : Kore.Proof.FunctionalityAxioms
Description : No-junk, No-confusion etc. for non-AC constructors
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Proof.FunctionalityAxioms
    ( generateFunctionalStatement
    , generateFunctionalHeadAxiom
    , proveFunctional
    , forallElimFunctional
    , forallElimFunctionalN
    ) where

import qualified Data.Functor.Foldable as Recursive

import Kore.AST.Pure
import Kore.AST.Valid
import Kore.Proof.Proof
import Kore.Proof.Util

-- | "a is functional" is encoded as "exists x. a = x"
generateFunctionalStatement
    :: Term
    -> Term
generateFunctionalStatement p =
    mkExists var (p `mkEquals_` (mkVar var))
        where var = "x" `varS` getSort p

-- | "f" is a functional head if
-- "forall x_1 .. x_n .
-- (exists x. x_1 = x) -> ... -> (exists x. x_n = x)
-- -> (exists x. f(x_1,...,x_n) = x)""
generateFunctionalHeadAxiom
    :: CofreeF
        (Application Object)
        (Valid Object)
        Term
    -> Term
generateFunctionalHeadAxiom (valid :< app) =
    mkForallN vars $ mkImpliesN
        (map generateFunctionalStatement vars')
        (generateFunctionalStatement $ mkApp patternSort head' vars')
  where
    Valid { patternSort } = valid
    Application { applicationSymbolOrAlias = head' } = app
    Application { applicationChildren = children } = app
    (vars, vars') = generateVarList (getSort <$> children) "x"

-- | Attempts to prove a given symbol a is functional
-- I.e. attempts to prove "exists x. a = x"
-- It uses the functionalVariable axiom,
-- and assumes everything else it needs.
proveFunctional
   :: Term
   -> Proof
proveFunctional term@(Recursive.project -> valid :< pattern') =
    case pattern' of
        VariablePattern var ->
            useRule $ FunctionalVar var (varS "x" patternSort)
        ApplicationPattern app ->
            let hFunctional =
                    forallElimFunctionalN'
                        csFunctional
                        applicationChildren
                        (assume $ generateFunctionalHeadAxiom $ valid :< app)
                csFunctional =
                    map proveFunctional applicationChildren
            in modusPonensN csFunctional hFunctional
          where
            Application { applicationChildren } = app
        _ -> assume $ generateFunctionalStatement term
  where
    Valid { patternSort } = valid

-- | Length-1 version of forallElimFunctionalN'
forallElimFunctional'
    :: Proof
    -> Term
    -> Proof
    -> Proof
forallElimFunctional' argIsFunctional arg pat =
    case getConclusion pat of
        Forall_ _ v p ->
            let ax = useRule $ FunctionalSubst v p argIsFunctionalVar arg
                Exists_ _ argIsFunctionalVar _ = getConclusion argIsFunctional
            in modusPonensN [pat, argIsFunctional] ax
        _ -> impossible

-- | Instantiates a term with a list of foralls,
-- i.e. a term of the form
-- "forall x_1 . ... forall x_n. p"
-- with a list of patterns, also requiring their functionality proofs.
forallElimFunctionalN'
    :: [Proof]
    -> [Term]
    -> Proof
    -> Proof
forallElimFunctionalN' argsAreFunctional args pat =
    foldr
      (\(arg, argIsFunctional) p ->
          forallElimFunctional' argIsFunctional arg p
      )
      pat
      (reverse (args `zip` argsAreFunctional))

-- | Length-1 version of forallElimFunctionalN
forallElimFunctional
    :: Term
    -> Proof
    -> Proof
forallElimFunctional arg pat =
    case getConclusion pat of
        Forall_ _ v p ->
            let ax =
                    useRule $ FunctionalSubst
                        v
                        p
                        (varS "x" $ sortedVariableSort v)
                        arg
            in modusPonensN [pat, assume $ generateFunctionalStatement arg] ax
        _ -> impossible


-- | Instantiates a term with many foralls,
-- i.e. a term of the form
-- "forall x_1 . ... forall x_n. p"
-- with a list of N patterns, assuming they are functional.
forallElimFunctionalN
    :: [Term]
    -> Proof
    -> Proof
forallElimFunctionalN args pat =
    foldr (\arg p -> forallElimFunctional arg p) pat $ reverse args
