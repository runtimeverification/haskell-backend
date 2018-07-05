{-|
Module      : Data.Kore.Proof.Substitution
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


module Data.Kore.Proof.Substitution where


import           Control.Applicative
import           Control.Lens
import           Control.Monad.State

import qualified Data.Set as S
import           Data.Maybe
import           Data.Fix
import           Data.Reflection
import           Data.Foldable
import           Data.List


import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML

import           Data.Kore.Variables.Free
import           Data.Kore.Proof.SmartConstructors

import           Data.Kore.Unparser.Unparse

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
                   [Variable (Id (name ++ show n) loc) sort | n <- [0..] ]

subTest :: CommonPurePattern Object 
subTest = dummyEnvironment @Object $ 
  subst (Var_ $ var "hi") (Var_ $ var "hello") $ 
  mkExists (var "ho") (Var_ $ var "hi")


-- localInPattern 
--    :: MetaOrObject level 
--    => Path 
--    -> (CommonPurePattern level -> CommonPurePattern level)
--    -> CommonPurePattern level 
--    -> CommonPurePattern level 
-- localInPattern []     f pat = f pat
-- localInPattern (n:ns) f pat = Fix $
--   case unFix pat of
--     AndPattern (And s1 a b) 
--       -> AndPattern $ case n of 
--            0 -> And s1 (localInPattern ns f a) b
--            1 -> And s1 a (localInPattern ns f b)
--            m -> error ("No " ++ show m ++ " position")
--     ApplicationPattern (Application head children)
--       -> let (a, b : bs) = splitAt n children 
--              children'   = a ++ [localInPattern ns f b] ++ bs 
--          in ApplicationPattern (Application head $ children')
--     CeilPattern (Ceil s1 s2 a) 
--       -> CeilPattern $ Ceil s1 s2 (localInPattern ns f a)
--     DomainValuePattern (DomainValue s1 a) 
--       -> DomainValuePattern $ DomainValue s1 (localInPattern ns f a)
--     EqualsPattern (Equals s1 s2 a b)
--       -> EqualsPattern $ case n of 
--            0 -> Equals s1 s2 (localInPattern ns f a) b 
--            1 -> Equals s1 s2 a (localInPattern ns f b)
--            m -> error ("No " ++ show m ++ " position")
--     ExistsPattern (Exists s1 v a) 
--       -> ExistsPattern $ Exists s1 v (localInPattern ns f a)
--     FloorPattern (Floor s1 s2 a)
--       -> FloorPattern $ Floor s1 s2 (localInPattern ns f a)
--     ForallPattern (Forall s1 v a)
--       -> ForallPattern $ Forall s1 v (localInPattern ns f a)
--     IffPattern (Iff s1 a b)
--       -> IffPattern $ case n of 
--            0 -> Iff s1 (localInPattern ns f a) b 
--            1 -> Iff s1 a (localInPattern ns f b)
--            m -> error ("No " ++ show m ++ " position")
--     ImpliesPattern (Implies s1 a b)
--       -> ImpliesPattern $ case n of 
--           0 -> Implies s1 (localInPattern ns f a) b
--           1 -> Implies s1 a (localInPattern ns f b)
--           m -> error ("No " ++ show m ++ " position")
--     InPattern (In s1 s2 a b)
--       -> InPattern $ case n of 
--            0 -> In s1 s2 (localInPattern ns f a) b 
--            1 -> In s1 s2 a (localInPattern ns f b)
--            m -> error ("No " ++ show m ++ " position")
--     NextPattern (Next s1 a)
--       -> NextPattern $ Next s1 (localInPattern ns f a)
--     NotPattern (Not s1 a)
--       -> NotPattern $ Not s1 (localInPattern ns f a)
--     OrPattern (Or s1 a b)
--       -> OrPattern $ case n of 
--            0 -> Or s1 (localInPattern ns f a) b 
--            1 -> Or s1 a (localInPattern ns f b)
--            m -> error ("No " ++ show m ++ " position")
--     RewritesPattern (Rewrites s1 a b)
--       -> RewritesPattern $ case n of 
--            0 -> Rewrites s1 (localInPattern ns f a) b 
--            1 -> Rewrites s1 a (localInPattern ns f b)
--            m -> error ("No " ++ show m ++ " position")
--     _ -> error "FIXME: Add more constructors here"

childIx n = partsOf allChildren . ix n

localInPattern
  :: MetaOrObject level 
  => [Int] 
  -> (CommonPurePattern level -> CommonPurePattern level)
  -> CommonPurePattern level
  -> CommonPurePattern level 
localInPattern [] f pat = f pat 
localInPattern (n:ns) f pat = 
  pat & (partsOf allChildren . ix n) %~ (localInPattern ns f)
