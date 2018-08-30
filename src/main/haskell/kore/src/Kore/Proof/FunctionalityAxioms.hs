{-|
Module      : Kore.Proof.FunctionalityAxioms
Description : No-junk, No-confusion etc. for non-AC constructors
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeSynonymInstances      #-}

{-# OPTIONS_GHC -Wno-unused-matches    #-}
{-# OPTIONS_GHC -Wno-name-shadowing    #-}


module Kore.Proof.FunctionalityAxioms
( generateFunctionalStatement
, generateFunctionalHeadAxiom
, proveFunctional
, forallElimFunctional
, forallElimFunctionalN
) where

import Data.Reflection
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.IndexedModule.MetadataTools

import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns

import Kore.Proof.Proof
import Kore.Proof.Util

-- | "a is functional" is encoded as "exists x. a = x"
generateFunctionalStatement
    :: Given (SortTools Object)
    => Term
    -> Term
generateFunctionalStatement p =
    mkExists var (p `mkEquals` (mkVar var))
        where var = "x" `varS` getSort p

-- | "f" is a functional head if
-- "forall x_1 .. x_n .
-- (exists x. x_1 = x) -> ... -> (exists x. x_n = x)
-- -> (exists x. f(x_1,...,x_n) = x)""
generateFunctionalHeadAxiom
    :: Given (SortTools Object)
    => SymbolOrAlias Object
    -> Term
generateFunctionalHeadAxiom h =
    let c = symbolOrAliasParams h
        (vars, vars') = generateVarList c "x"
    in mkForallN vars $ mkImpliesN
           (map generateFunctionalStatement vars')
           (generateFunctionalStatement $ mkApp h vars')

-- | Attempts to prove a given symbol a is functional
-- I.e. attempts to prove "exists x. a = x"
-- It uses the functionalVariable axiom,
-- and assumes everything else it needs.
proveFunctional
   :: Given (SortTools Object)
   => Term
   -> Proof
proveFunctional p = case p of
    V v -> useRule $ FunctionalVar v ("x" `varS` getSort p)
    App_ h cs ->
        let hFunctional =
                forallElimFunctionalN'
                    csFunctional
                    cs
                    (assume $ generateFunctionalHeadAxiom h)
            csFunctional =
                map proveFunctional cs
        in modusPonensN csFunctional hFunctional
    x -> assume $ generateFunctionalStatement x

-- | Length-1 version of forallElimFunctionalN'
forallElimFunctional'
    :: Given (SortTools Object)
    => Proof
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
    :: Given (SortTools Object)
    => [Proof]
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
    :: Given (SortTools Object)
    => Term
    -> Proof
    -> Proof
forallElimFunctional arg pat =
    case getConclusion pat of
        Forall_ _ v p ->
            let ax =
                    useRule $ FunctionalSubst
                        v
                        p
                        ("x" `varS` getSort (V v))
                        arg
            in modusPonensN [pat, assume $ generateFunctionalStatement arg] ax
        _ -> impossible


-- | Instantiates a term with many foralls,
-- i.e. a term of the form
-- "forall x_1 . ... forall x_n. p"
-- with a list of N patterns, assuming they are functional.
forallElimFunctionalN
    :: Given (SortTools Object)
    => [Term]
    -> Proof
    -> Proof
forallElimFunctionalN args pat =
    foldr (\arg p -> forallElimFunctional arg p) pat $ reverse args
