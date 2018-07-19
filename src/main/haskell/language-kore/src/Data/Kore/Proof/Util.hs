{-|
Module      : Data.Kore.Proof.Proof
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
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

module Data.Kore.Proof.Util
( mkForallN
, forallIntroN
, forallElimN
, mkExistsN
, existsIntroN
, mkAndN
, andIntroN
, andElimN
, provablySubstitute
, eqSymmetry
, eqTransitivity
) where


import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Reflection

import           Data.Kore.Proof.Proof

-- | Helper functions for common proof steps.
-- Conventions:
-- Functions ending in `N` take or give a list
-- Functions beginning with `mk` construct a pattern, not a proof
-- Functions with `intro` or `elim` are N-ary versions
-- of the introduction and elimination rules.
-- i.e. mkAndN [a,b,c] = a `mkAnd` (b `mkAnd` c)
-- TODO: Some of these could be replaced with schemas
-- i.e. poor man's HOL

--------------------------------------------------------------------------------

mkForallN
    :: Given (MetadataTools Object)
    => [Var]
    -> Term
    -> Term
mkForallN vars pat =
    foldr mkForall pat vars

forallIntroN
    :: Given (MetadataTools Object)
    => [Var]
    -> Proof
    -> Proof
forallIntroN vars pat =
    foldr (\var p -> useRule $ Abstract var p) pat vars


forallElimN
    :: Given (MetadataTools Object)
    => [Term]
    -> Proof
    -> Proof
forallElimN args pat =
    foldr (\arg p -> useRule $ ForallElim arg p) pat $ reverse args

--------------------------------------------------------------------------------

mkExistsN
    :: Given (MetadataTools Object)
    => [Var]
    -> Term
    -> Term
mkExistsN vars pat =
    foldr mkExists pat vars

existsIntroN
    :: Given (MetadataTools Object)
    => [(Var, Term)]
    -> Proof
    -> Proof
existsIntroN terms pat =
    foldr (\(var, term) p -> useRule $ ExistsIntro var term p) pat terms

-- existsElimN
--     :: Given (MetadataTools Object)
--     => [(Var, Term)]
--     -> Proof
--     -> Proof
--     -> Proof
-- existsElimN terms existentialStmt pat =
--     let n = length terms
--         peelOffExist (Exists_ _ _ p) = p
--         peelOffExists =
--             take n
--           $ iterate peelOffExist
--           $ getConclusion existentialStmt
--     in peelOffExists undefined
    -- foldr
    -- (\(var, term) (exP, c) -> useRule $ ExistsElim exP var term p)
    -- (existentialStmt, pat)
    -- terms

--------------------------------------------------------------------------------

mkAndN
    :: Given (MetadataTools Object)
    => [Term]
    -> Term
mkAndN [] = mkTop
mkAndN es = foldr1 mkAnd es

andIntroN
    :: Given (MetadataTools Object)
    => [Proof]
    -> Proof
andIntroN [] = useRule TopIntro
andIntroN ps = foldr1 (\a b -> useRule $ AndIntro a b) ps

andElimN
    :: Given (MetadataTools Object)
    => Proof
    -> [Proof]
andElimN p = case getConclusion p of
    And_ _ _ _ ->
           andElimN (useRule $ AndElimL p)
        ++ andElimN (useRule $ AndElimR p)
    _ -> [p]

--------------------------------------------------------------------------------

provablySubstitute
    :: Given (MetadataTools Object)
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
    :: Given (MetadataTools Object)
    => Proof
    -> Proof
eqSymmetry = undefined

eqTransitivity
    :: Given (MetadataTools Object)
    => Proof
    -> Proof
    -> Proof
eqTransitivity = undefined


