{-|
Module      : Data.Kore.ASTUtils.Substitution
Description : Substitute phi_1 for phi_2, avoiding capture
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : phillip.harris@runtimeverification.com
Stability   : experimental
Portability : portable
-}

{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE Rank2Types             #-}
{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Data.Kore.ASTUtils.Substitution where


import           Control.Lens

import qualified Data.Set as S
import           Data.Fix
import           Data.List


import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML

import           Data.Kore.ASTUtils.SmartConstructors


subst
  :: MetaOrObject level 
  => CommonPurePattern level 
  -> CommonPurePattern level 
  -> CommonPurePattern level 
  -> CommonPurePattern level
subst a b (Forall_ s1 v p) = handleBinder a b Forall_ s1 v p
subst a b (Exists_ s1 v p) = handleBinder a b Exists_ s1 v p
subst a b pat =
  if pat == a then b else Fix $ fmap (subst a b) $ unFix pat

handleBinder
  :: MetaOrObject level 
  => CommonPurePattern level 
  -> CommonPurePattern level 
  -> (Sort level -> Variable level -> CommonPurePattern level -> CommonPurePattern level)
  -> Sort level 
  -> Variable level 
  -> CommonPurePattern level 
  -> CommonPurePattern level 
handleBinder a b binder s1 v p = 
  let fa = freeVars a 
      fb = freeVars b
  in if S.member v fa 
    then binder s1 v p 
  else if S.member v fb
    then subst a b $ alphaRename $ binder s1 v p 
    else binder s1 v $ subst a b p

freeVars
  :: MetaOrObject level 
  => CommonPurePattern level
  -> S.Set (Variable level)
freeVars (Forall_ s1 v p) = S.delete v $ freeVars p 
freeVars (Exists_ s1 v p) = S.delete v $ freeVars p 
freeVars (Var_ v) = S.singleton v 
freeVars p = S.unions $ map freeVars $ p ^. partsOf allChildren

alphaRename
  :: MetaOrObject level 
  => CommonPurePattern level 
  -> CommonPurePattern level 
alphaRename = (\case 
 Forall_ s1 v p -> go Forall_ s1 v p 
 Exists_ s1 v p -> go Exists_ s1 v p
 _ -> error "Input must be an Exist or Forall at the top level"
 ) where go binder s1 v p = 
           binder s1 replacementVar 
           (subst (Var_ v) (Var_ replacementVar) p)
           where replacementVar = head $ alternatives v \\ (S.toList $ freeVars p)
                 alternatives (Variable (Id name loc) sort) =  -- FIXME: lens. 
                   [Variable (Id (name ++ show n) loc) sort | n <- [(0::Integer)..] ]

inPath
  :: (MetaOrObject level, Applicative f)
  => [Int]
  -> (CommonPurePattern level -> f (CommonPurePattern level))
  -> (CommonPurePattern level -> f (CommonPurePattern level))
inPath [] = id --aka the identity lens
inPath (n : ns) = partsOf allChildren . ix n . inPath ns 

localSubst
  :: MetaOrObject level 
  => CommonPurePattern level 
  -> CommonPurePattern level 
  -> [Int]
  -> CommonPurePattern level 
  -> CommonPurePattern level
localSubst a b path pat = pat & (inPath path) %~ (subst a b)

localInPattern
  :: MetaOrObject level 
  => [Int] 
  -> (CommonPurePattern level -> CommonPurePattern level)
  -> CommonPurePattern level
  -> CommonPurePattern level 
localInPattern [] f pat = f pat 
localInPattern (n:ns) f pat = 
  pat & (partsOf allChildren . ix n) %~ (localInPattern ns f)
