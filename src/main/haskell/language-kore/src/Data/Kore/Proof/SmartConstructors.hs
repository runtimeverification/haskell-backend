{-|
Module      : Data.Kore.Proof.SmartConstructors
Description : Tree-based proof system, which can be
              hash-consed into a list-based one.
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
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE PatternSynonyms        #-}

module Data.Kore.Proof.SmartConstructors where


import           Control.Applicative
import           Control.Lens
import           Control.Monad.State

import           Data.Maybe
import           Data.Fix
import           Data.Reflection
import           Data.Foldable


import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML


getSort 
  :: (MetaOrObject level, Given (MetadataTools level))
  => CommonPurePattern level
  -> Sort level
getSort x = (getPatternResultSort (getResultSort given) $ unFix x)

flexibleSort 
  :: MetaOrObject level 
  => Sort level
flexibleSort =
  SortVariableSort $ SortVariable 
    { getSortVariable = noLocationId "__FlexibleSort__" } --FIXME

getRigidSort 
  :: (MetaOrObject level, Given (MetadataTools level))
  => CommonPurePattern level 
  -> Maybe (Sort level)
getRigidSort p = 
  case forceSort flexibleSort p of 
    Nothing -> Just $ getSort p 
    Just _  -> Nothing

-- isRigid p = case unFix p of 
--   ApplicationPattern _ -> True
--   DomainValuePattern _ -> True
--   ExistsPattern _      -> True
--   ForallPattern _      -> True
--   IffPattern _         -> True 
--   ImpliesPattern _     -> True
--   NextPattern _        -> True 
--   NotPattern _         -> True 
--   OrPattern _          -> True 
--   RewritesPattern _    -> True 
--   _ -> False

--TODO: make "sortRelevantChildren" and "resultSort" lenses. 
forceSort 
  :: MetaOrObject level
  => Sort level 
  -> CommonPurePattern level
  -> Maybe (CommonPurePattern level)
forceSort s p = Fix <$> 
  case unFix p of 
    AndPattern (And _ a b) -> do 
      a' <- forceSort s a 
      b' <- forceSort s b 
      return $ AndPattern (And s a' b')
    BottomPattern (Bottom _) -> 
      return $ BottomPattern (Bottom s)
    CeilPattern (Ceil s1 _ a) -> 
      return $ CeilPattern (Ceil s1 s a)
    EqualsPattern (Equals s1 _ a b) -> 
      return $ EqualsPattern (Equals s1 s a b)
    ExistsPattern (Exists s1 v a) -> do
      a' <- forceSort s a 
      return $ ExistsPattern (Exists s v a)
    FloorPattern (Floor s1 _ a) -> 
      return $ FloorPattern (Floor s1 s a)
    ForallPattern (Forall s1 v a) -> do
      a' <- forceSort s a 
      return $ ForallPattern (Forall s v a) 
    IffPattern (Iff s1 a b) -> do 
      a' <- forceSort s a 
      b' <- forceSort s b 
      return $ IffPattern (Iff s a' b')  
    ImpliesPattern (Implies s1 a b) -> do 
      a' <- forceSort s a 
      b' <- forceSort s b 
      return $ ImpliesPattern (Implies s a' b')  
    InPattern (In s1 _ a b) ->
      return $ InPattern (In s1 s a b)
    NextPattern (Next _ a) -> do 
      a' <- forceSort s a 
      return $ NextPattern (Next s a')
    NotPattern (Not _ a) -> do 
      a' <- forceSort s a 
      return $ NotPattern (Not s a')
    OrPattern (Or _ a b) -> do 
      a' <- forceSort s a 
      b' <- forceSort s b 
      return $ OrPattern (Or s a' b')
    RewritesPattern (Rewrites _ a b) -> do 
      a' <- forceSort s a 
      b' <- forceSort s b 
      return $ RewritesPattern (Rewrites s a' b')
    TopPattern (Top _) -> 
      return $ TopPattern (Top s)
    _ -> Nothing 
    -- we can't change the sort of an application
    -- OR CAN WE???

makeSortsAgree ps = 
  forM ps . forceSort $ 
    case asum $ map getRigidSort ps of 
      Nothing -> flexibleSort
      Just a -> a

mkAnd a' b' = 
  let Just [a,b] = makeSortsAgree [a',b']
  in Fix $ AndPattern $ And (getSort a) a b

mkApp h c = Fix $ ApplicationPattern $ Application h c 

mkBottom 
  :: MetaOrObject level
  => CommonPurePattern level 
mkBottom = Fix $ BottomPattern $ Bottom flexibleSort 

mkCeil 
  :: (MetaOrObject level, Given (MetadataTools level))
  => CommonPurePattern level 
  -> CommonPurePattern level 
mkCeil a = Fix $ CeilPattern $ Ceil (getSort a) flexibleSort a

mkDomainValue
  :: (MetaOrObject Object, Given (MetadataTools Object))
  => CommonPurePattern Object 
  -> CommonPurePattern Object 
mkDomainValue a = Fix $ DomainValuePattern $ DomainValue (getSort a) a

mkEquals
  :: (MetaOrObject level, Given (MetadataTools level))
  => CommonPurePattern level 
  -> CommonPurePattern level 
  -> CommonPurePattern level 
mkEquals a' b' = 
  let Just [a,b] = makeSortsAgree [a',b']
  in Fix $ EqualsPattern $ Equals (getSort a) flexibleSort a b 


