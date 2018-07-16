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



module Data.Kore.Proof.Util where

import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Data.Fix
import           Data.Fix
import           Data.Foldable
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.IndexedModule.MetadataTools
import qualified Data.Map.Strict                       as M
import           Data.Maybe
import           Data.Reflection
import qualified Data.Set                              as S


import           Data.Kore.Proof.Proof


import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.ASTUtils.Substitution

import           Debug.Trace

--------------------------------------------------------------------------------

mkForallN
    :: Given (MetadataTools Object)
    => [Var]
    -> Term
    -> Term
mkForallN vars pat =
    foldr mkForall pat vars

forallN
    :: Given (MetadataTools Object)
    => [Var]
    -> Term
    -> Term
forallN vars pat = foldr mkForall pat vars

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

existsElimN
    :: Given (MetadataTools Object)
    => [(Var, Term)]
    -> Proof
    -> Proof
    -> Proof
existsElimN terms existentialStmt pat =
    let n = length terms
        peelOffExist (Exists_ _ _ p) = p
        peelOffExists =
            take n
          $ iterate peelOffExist
          $ getConclusion existentialStmt
    in traceShow peelOffExists undefined
    -- foldr
    -- (\(var, term) (exP, c) -> useRule $ ExistsElim exP var term p)
    -- (existentialStmt, pat)
    -- terms

--------------------------------------------------------------------------------

andN
    :: Given (MetadataTools Object)
    => [Term]
    -> Term
andN [] = mkTop
andN es = foldr1 mkAnd es

andIntroN
    :: Given (MetadataTools Object)
    => [Proof]
    -> Proof
andIntroN [] = useRule TopIntro
andIntroN ps = foldr1 (\a b -> useRule $ AndIntro a b) ps

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
