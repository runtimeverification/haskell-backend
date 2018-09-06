{-|
Module      : Kore.Proof.Util
Description : Helper functions for common proof steps.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable

Conventions:
Functions ending in `N` take or give a list
Functions beginning with `mk` construct a pattern, not a proof
Functions with `intro` or `elim` are N-ary versions
of the introduction and elimination rules.
i.e. mkAndN [a,b,c] = a `mkAnd` (b `mkAnd` c)
TODO: Some of these could be replaced with schemas
i.e. poor man's HOL
-}

{-# LANGUAGE AllowAmbiguousTypes       #-}
{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DeriveFoldable            #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DeriveTraversable         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FunctionalDependencies    #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# OPTIONS_GHC -Wno-unused-matches    #-}
{-# OPTIONS_GHC -Wno-name-shadowing    #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns  #-}

module Kore.Proof.Util
(
-- * General deduction tools
  modusPonensN
, mkImpliesN
, tryDischarge
, tryDischargeN
-- * Forall
, mkForallN
, forallIntroN
, forallElimN
-- * Exists
, mkExistsN
, existsIntroN
-- * Connectives
, mkAndN
, mkOrN
, andIntroN
, andElimN
-- * Equality
, provablySubstitute
, eqSymmetry
, eqTransitivity
, generateVarList
) where

import Data.Reflection
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.ASTUtils.SmartConstructors
import Kore.ASTUtils.SmartPatterns
import Kore.IndexedModule.MetadataTools

import Kore.Proof.Proof

modusPonensN
    :: Given (SortTools Object)
    => [Proof]
    -> Proof
    -> Proof
modusPonensN as b =
    foldl (\b a -> useRule $ ModusPonens a b) b as

mkImpliesN
    :: Given (SortTools Object)
    => [Term]
    -> Term
    -> Term
mkImpliesN as b =
    foldr (\a b -> a `mkImplies` b) b as

tryDischarge
    :: Given (SortTools Object)
    => Proof
    -> Proof
    -> Proof
tryDischarge a b =
    if a' == b'
    then a
    else useRule $ fmap (tryDischarge a) $ getJustification b
      where a' = getConclusion a
            b' = getConclusion b

tryDischargeN
    :: Given (SortTools Object)
    => [Proof]
    -> Proof
    -> Proof
tryDischargeN as b = foldr tryDischarge b as

--------------------------------------------------------------------------------

mkForallN
    :: Given (SortTools Object)
    => [Var]
    -> Term
    -> Term
mkForallN vars pat =
    foldr mkForall pat vars

forallIntroN
    :: Given (SortTools Object)
    => [Var]
    -> Proof
    -> Proof
forallIntroN vars pat =
    foldr (\var p -> useRule $ Abstract var p) pat vars


forallElimN
    :: Given (SortTools Object)
    => [Term]
    -> Proof
    -> Proof
forallElimN args pat =
    foldr (\arg p -> useRule $ ForallElim arg p) pat $ reverse args

--------------------------------------------------------------------------------

mkExistsN
    :: Given (SortTools Object)
    => [Var]
    -> Term
    -> Term
mkExistsN vars pat =
    foldr mkExists pat vars

existsIntroN
    :: Given (SortTools Object)
    => [(Var, Term)]
    -> Proof
    -> Proof
existsIntroN terms pat =
    foldr (\(var, term) p -> useRule $ ExistsIntro var term p) pat terms

--------------------------------------------------------------------------------

mkAndN
    :: Given (SortTools Object)
    => [Term]
    -> Term
mkAndN [] = mkTop
mkAndN es = foldr1 mkAnd es

andIntroN
    :: Given (SortTools Object)
    => [Proof]
    -> Proof
andIntroN [] = useRule TopIntro
andIntroN ps = foldr1 (\a b -> useRule $ AndIntro a b) ps

andElimN
    :: Given (SortTools Object)
    => Proof
    -> [Proof]
andElimN p = case getConclusion p of
    And_ _ _ _ ->
           andElimN (useRule $ AndElimL p)
        ++ andElimN (useRule $ AndElimR p)
    _ -> [p]

--------------------------------------------------------------------------------

mkOrN
    :: Given (SortTools Object)
    => [Term]
    -> Term
mkOrN [] = mkBottom
mkOrN es = foldr1 mkOr es

--------------------------------------------------------------------------------

provablySubstitute
    :: Given (SortTools Object)
    => Proof
    -> Path
    -> Proof
    -> Proof
provablySubstitute eq path pat = case getConclusion eq of
    Equals_ _ _ a b ->
      useRule $ ModusPonens
        pat
        (useRule $ ModusPonens
            eq
            (useRule $ EqualityElim
                a
                b
                (getConclusion pat)
                path
            )
        )
    _ -> impossible

eqSymmetry
    :: Given (SortTools Object)
    => Proof
    -> Proof
eqSymmetry = undefined

eqTransitivity
    :: Given (SortTools Object)
    => Proof
    -> Proof
    -> Proof
eqTransitivity = undefined

--------------------------------------------------------------------------------

generateVarList
    :: Given (SortTools Object)
    => [Sort Object]
    -> String
    -> ([Variable Object], [Term])
generateVarList sorts name =
    let vars =
          zipWith
            (\n sort -> varS (name ++ show n) sort)
            [(1::Int)..]
            sorts
        vars' = map Var_ vars
    in (vars, vars')
