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
) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Reflection

import           Data.Kore.ASTUtils.SmartConstructors

import           Data.Kore.Proof.Dummy
import           Data.Kore.Proof.Proof
import           Data.Kore.Proof.Util

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
    -> [Sort Object] 
    -> Term 
generateFunctionalHeadAxiom h c = 
    let (vars, vars') = generateVarList c "x"
    in mkForallN vars $ generateFunctionalStatement $ mkApp h vars'

-- proveFunctional 
   -- :: Given (MetadataTools Object)

