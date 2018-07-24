{-|
Module      : Data.Kore.Proof.FunctionalityAxioms
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


module Data.Kore.Proof.FunctionalityAxioms
( generateFunctionalStatement
, generateFunctionalHeadAxiom
, proveFunctional
) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Reflection

import           Data.Kore.ASTUtils.SmartConstructors

import           Data.Kore.Proof.Dummy
import           Data.Kore.Proof.Proof
import           Data.Kore.Proof.Util

import Debug.Trace
import Data.Text.Prettyprint.Doc

pTrace x = trace (show $ pretty x) x 

generateFunctionalStatement
    :: Given (MetadataTools Object)
    => Term 
    -> Term 
generateFunctionalStatement p = 
    mkExists var (p `mkEquals` (mkVar var))
        where var = varS "x" $ getSort p

generateFunctionalHeadAxiom
    :: Given (MetadataTools Object)
    => SymbolOrAlias Object 
    -> Term 
generateFunctionalHeadAxiom h = 
    let c = symbolOrAliasParams h 
        (vars, vars') = generateVarList c "x"
    in mkForallN vars $ mkImpliesN 
           (map generateFunctionalStatement vars') 
           (generateFunctionalStatement $ mkApp h vars')

proveFunctional 
   :: Given (MetadataTools Object)
   => Term 
   -> Proof 
proveFunctional p = case p of 
    App_ h cs -> 
        let hFunctional = forallElimN cs (assume $ generateFunctionalHeadAxiom h)
            csFunctional = map proveFunctional cs 
        in modusPonensN csFunctional hFunctional
    Var_ v -> useRule $ FunctionalVar v (varS "x" $ getSort $ Var_ v)
    x -> assume $ generateFunctionalStatement x 

