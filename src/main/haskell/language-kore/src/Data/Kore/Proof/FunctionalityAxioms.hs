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
, forallElimFunctional
, forallElimFunctionalN
) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Reflection

import           Data.Kore.ASTUtils.SmartConstructors

import           Data.Kore.Proof.Proof
import           Data.Kore.Proof.Util

generateFunctionalStatement
    :: Given (MetadataTools Object)
    => Term
    -> Term
generateFunctionalStatement p =
    mkExists var (p `mkEquals` (mkVar var))
        where var = "x" `varS` getSort p

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

forallElimFunctional'
    :: Given (MetadataTools Object)
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

forallElimFunctionalN'
    :: Given (MetadataTools Object)
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

forallElimFunctional
    :: Given (MetadataTools Object)
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

-- printLineProof $ dummyEnvironment $ proveFunctional $ mkApp (symS "f" [testSort "*", testSort "*"]) [mkVar $ var "a", mkVar $ var "b"]

forallElimFunctionalN
    :: Given (MetadataTools Object)
    => [Term]
    -> Proof
    -> Proof
forallElimFunctionalN args pat =
    foldr (\arg p -> forallElimFunctional arg p) pat $ reverse args
