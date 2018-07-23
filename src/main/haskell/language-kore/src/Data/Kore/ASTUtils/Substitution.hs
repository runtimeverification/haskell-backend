{-|
Module      : Data.Kore.ASTUtils.Substitution
Description : Substitute phi_1 for phi_2, avoiding capture
              In particular this implements axiom 7 in
              the "large" axiom set (Rosu 2017).
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Kore.ASTUtils.Substitution
( subst
, localSubst
)
where


import           Control.Lens

import           Data.Fix
import qualified Data.Set                             as S

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML

import           Data.Kore.ASTUtils.SmartConstructors

-- | subst phi_1 phi_2 phi = phi[phi_2/phi_1]
-- Note that different papers use different conventions.
-- Here `phi_1` is the old pattern that disappears
-- and `phi_2` is the new pattern that replaces it.
subst
    :: MetaOrObject level
    => CommonPurePattern level
    -> CommonPurePattern level
    -> CommonPurePattern level
    -> CommonPurePattern level
subst old new = \case
    Forall_ s1 v p -> handleBinder old new Forall_ s1 v p
    Exists_ s1 v p -> handleBinder old new Exists_ s1 v p
    pat
     | pat == old -> new
     | otherwise  -> Fix $ fmap (subst old new) $ unFix pat

-- subst2 a b = cata (\pat -> if Fix pat == a then b else Fix pat)

-- handleBinder
--     :: MetaOrObject level
--     => CommonPurePattern level
--     -> CommonPurePattern level
--     -> ( Sort level
--       -> Variable level
--       -> CommonPurePattern level
--       -> CommonPurePattern level
--       )
--     -> Sort level
--     -> Variable level
--     -> CommonPurePattern level
--     -> CommonPurePattern level
-- handleBinder old new binder s1 v p =
--     let fa = freeVars old
--         fb = freeVars new
--     in if S.member v fa
--         then binder s1 v p
--     else if S.member v fb
--         then subst old new $ alphaRename $ binder s1 v p
--         else binder s1 v $ subst old new p

handleBinder old new binder s1 v p
  | S.member v (freeVars old) = binder s1 v p
  | S.member v (freeVars new) = subst old new $ alphaRename binder s1 v p
  | otherwise = binder s1 v $ subst old new p
  where
    alphaRename binder s1 v p =
        binder s1 (replacementVar v p)
        (subst (Var_ v) (Var_ $ replacementVar v p) p)
    replacementVar v p =
        head $ filter (not . flip S.member freeVarsP) $ alternatives v
    freeVarsP = freeVars p
    alternatives (Variable (Id name loc) sort) =
        [Variable (Id (name ++ show n) loc) sort | n <- [(0::Integer)..] ]

freeVars
    :: MetaOrObject level
    => CommonPurePattern level
    -> S.Set (Variable level)
freeVars = \case
    Forall_ s1 v p -> S.delete v $ freeVars p
    Exists_ s1 v p -> S.delete v $ freeVars p
    Var_ v -> S.singleton v
    p -> S.unions $ map freeVars $ p ^. partsOf allChildren

-- | Apply a substitution at every eligible position below the specified path.
-- This is technically less general than axiom 7, which allows for
-- substituting at an arbitrary set of eligible positions,
-- but it doesn't matter in practice.
localSubst
    :: MetaOrObject level
    => CommonPurePattern level
    -> CommonPurePattern level
    -> [Int]
    -> CommonPurePattern level
    -> CommonPurePattern level
localSubst a b path pat = localInPattern path (subst a b) pat


