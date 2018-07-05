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
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveFoldable         #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Data.Kore.Proof.SmartConstructors where


import           Control.Applicative
import           Control.Lens
import           Control.Monad.State

import           Data.Hashable
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


import Debug.Trace

-- instance Hashable (CommonPurePattern Object)

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

isRigid p = case unFix p of 
  ApplicationPattern _ -> True
  DomainValuePattern _ -> True
  VariablePattern    _ -> True
  _ -> False

isFlexible p = case unFix p of
  BottomPattern _ -> True 
  CeilPattern   _ -> True 
  EqualsPattern _ -> True 
  FloorPattern  _ -> True 
  InPattern     _ -> True 
  TopPattern    _ -> True 
  _ -> False

pattern And_          s2   a b = Fix (AndPattern (And s2 a b))
pattern App_ h c               = Fix (ApplicationPattern (Application h c))
pattern Bottom_       s2       = Fix (BottomPattern (Bottom s2))
pattern Ceil_      s1 s2   a   = Fix (CeilPattern (Ceil s1 s2 a))
pattern DV_           s2   a   = Fix (DomainValuePattern (DomainValue s2 a))
pattern Equals_    s1 s2   a b = Fix (EqualsPattern (Equals s1 s2 a b))
pattern Exists_       s2 v a   = Fix (ExistsPattern (Exists s2 v a))
pattern Floor_     s1 s2   a   = Fix (FloorPattern (Floor s1 s2 a))
pattern Forall_       s2 v a   = Fix (ForallPattern (Forall s2 v a))
pattern Iff_          s2   a b = Fix (IffPattern (Iff s2 a b))
pattern Implies_      s2   a b = Fix (ImpliesPattern (Implies s2 a b))
pattern In_        s1 s2   a b = Fix (InPattern (In s1 s2 a b))
pattern Next_         s2   a   = Fix (NextPattern (Next s2 a)) 
pattern Not_          s2   a   = Fix (NotPattern (Not s2 a))
pattern Or_           s2   a b = Fix (OrPattern (Or s2 a b))
pattern Rewrites_     s2   a b = Fix (RewritesPattern (Rewrites s2 a b))
pattern Top_          s2       = Fix (TopPattern (Top s2))
pattern Var_             v     = Fix (VariablePattern v)   

patternLens
  :: (Applicative f, MetaOrObject level) 
  => (Sort level -> f (Sort level))
  -> (Sort level -> f (Sort level))
  -> (Variable level -> f (Variable level))
  -> (CommonPurePattern level -> f (CommonPurePattern level))
  -> (CommonPurePattern level -> f (CommonPurePattern level))
  -> (CommonPurePattern level -> f (CommonPurePattern level))
patternLens 
  i  --input sort
  o -- result sort
  var -- variable
  r -- Rigid children, i.e. those whose sort must match the result sort
  f --flexible children, i.e. those whose sort can be anything
  = \case 
  And_       s2   a b -> And_      <$>          o s2           <*> r a <*> r b
  Bottom_    s2       -> Bottom_   <$>          o s2
  Ceil_   s1 s2   a   -> Ceil_     <$> i s1 <*> o s2           <*> f a
  DV_        s2   a   -> DV_       <$>          o s2           <*> r a
  Equals_ s1 s2   a b -> Equals_   <$> i s1 <*> o s2           <*> r a <*> r b
  Exists_    s2 v a   -> Exists_   <$>          o s2 <*> var v <*> r a
  Floor_  s1 s2   a   -> Floor_    <$> i s1 <*> o s2           <*> f a
  Forall_    s2 v a   -> Forall_   <$>          o s2 <*> var v <*> r a
  Iff_       s2   a b -> Iff_      <$>          o s2           <*> r a <*> r b
  Implies_   s2   a b -> Implies_  <$>          o s2           <*> r a <*> r b
  In_     s1 s2   a b -> In_       <$> i s1 <*> o s2           <*> f a <*> f b
  Next_      s2   a   -> Next_     <$>          o s2           <*> r a
  Not_       s2   a   -> Not_      <$>          o s2           <*> r a
  Or_        s2   a b -> Or_       <$>          o s2           <*> r a <*> r b
  Rewrites_  s2   a b -> Rewrites_ <$>          o s2           <*> r a <*> r b
  Top_       s2       -> Top_      <$>          o s2
  Var_          v     -> Var_      <$>                   var v
 
resultSort       f = patternLens pure f    pure pure pure
inputSort        f = patternLens f    pure pure pure pure
rigidChildren    f = patternLens pure pure pure f    pure
flexibleChildren f = patternLens pure pure pure pure f
allChildren      f = patternLens pure pure pure f    f
-- resultSort f           = sortRelevantChildrenLens pure f pure 
-- sortRelevantChildren f = sortRelevantChildrenLens pure pure f

forceSort 
  :: (MetaOrObject level, Given (MetadataTools level))
  => Sort level 
  -> CommonPurePattern level
  -> Maybe (CommonPurePattern level)
forceSort s p = 
  if isRigid p
    then checkAlreadyCorrectSort s p
  else if isFlexible p 
    then Just $ p & resultSort .~ s
    else traverseOf rigidChildren (forceSort s) p

checkAlreadyCorrectSort s p
 | getSort p == s = Just p 
 | otherwise = Nothing


makeSortsAgree
  :: (MetaOrObject level, Given (MetadataTools level))
  => [CommonPurePattern level]
  -> Maybe [CommonPurePattern level]
makeSortsAgree ps = 
  forM ps $ forceSort $ 
    case asum $ getRigidSort <$> ps of 
      Nothing -> flexibleSort
      Just a  -> a

spy x = trace (show x) x

-- ensures that the subpatterns of a pattern match in their sorts
-- and assigns the correct sort to the top level pattern
-- i.e. converts the invalid (x : Int /\ ( x < 3 : Float)) : Bool
-- to the valid (x : Int /\ (x < 3 : Int)) : Int
ensureSortAgreement
  :: (MetaOrObject level, Given (MetadataTools level))
  => CommonPurePattern level 
  -> CommonPurePattern level 
ensureSortAgreement p = 
  case makeSortsAgree $ p ^. partsOf rigidChildren of 
    Just []       -> p
    Just children -> 
      p & (partsOf rigidChildren) .~ children 
        & resultSort .~ (getSort $ head children)
        & inputSort  .~ (getSort $ head children)
    Nothing -> error $ "Can't unify sorts of subpatterns: " ++ show p


mkAnd a b = ensureSortAgreement $ And_ fixmeSort a b

mkApp h c = App_ h c 

mkBottom 
  :: MetaOrObject level
  => CommonPurePattern level 
mkBottom = Bottom_ flexibleSort 

mkCeil 
  :: (MetaOrObject level, Given (MetadataTools level))
  => CommonPurePattern level 
  -> CommonPurePattern level 
mkCeil a = Ceil_ (getSort a) flexibleSort a

mkDomainValue
  :: (MetaOrObject Object, Given (MetadataTools Object))
  => CommonPurePattern Object 
  -> CommonPurePattern Object 
mkDomainValue a = DV_ (getSort a) a

mkEquals
  :: (MetaOrObject level, Given (MetadataTools level))
  => CommonPurePattern level 
  -> CommonPurePattern level 
  -> CommonPurePattern level 
mkEquals a b = ensureSortAgreement $ Equals_ fixmeSort fixmeSort a b

mkExists v a = ensureSortAgreement $ Exists_ fixmeSort v a 

mkFloor a = ensureSortAgreement $ Floor_ fixmeSort fixmeSort a 

mkForall v a = ensureSortAgreement $ Forall_ fixmeSort v a 

mkIff a b = ensureSortAgreement $ Iff_ fixmeSort a b 

mkImplies a b = ensureSortAgreement $ Implies_ fixmeSort a b 

mkIn a b = ensureSortAgreement $ In_ fixmeSort fixmeSort a b 

mkNext
  :: (MetaOrObject Object, Given (MetadataTools Object))
  => CommonPurePattern Object 
  -> CommonPurePattern Object 
mkNext a = ensureSortAgreement $ Next_ fixmeSort a 

mkNot a = ensureSortAgreement $ Not_ fixmeSort a 

mkOr a b = ensureSortAgreement $ Or_ fixmeSort a b 

mkRewrites
  :: (MetaOrObject Object, Given (MetadataTools Object))
  => CommonPurePattern Object 
  -> CommonPurePattern Object 
  -> CommonPurePattern Object
mkRewrites a b = ensureSortAgreement $ Rewrites_ fixmeSort a b 

mkTop
  :: (MetaOrObject level, Given (MetadataTools level))
  => CommonPurePattern level 
mkTop = Top_ flexibleSort

mkVar = Var_

test :: CommonPurePattern Object
test = dummyEnvironment @Object testPattern

testPattern :: Given (MetadataTools Object) => CommonPurePattern Object
testPattern = 
  mkOr 
  (mkExists (Variable (noLocationId "a") placeholderSort) 
    (mkVar (Variable (noLocationId "A") placeholderSort)) )
  (mkVar (Variable (noLocationId "A") placeholderSort))

dummyEnvironment
  :: forall level r . MetaOrObject level => (Given (MetadataTools level) => r) -> r
dummyEnvironment = give (dummyMetadataTools @level)

dummyMetadataTools 
  :: MetaOrObject level 
  => MetadataTools level
dummyMetadataTools = MetadataTools
    { isConstructor    = const True 
    , isFunctional     = const True 
    , getArgumentSorts = const [] 
    , getResultSort    = const placeholderSort
    }

var :: MetaOrObject level => String -> Variable level
var x = 
  Variable (noLocationId x) placeholderSort 

placeholderSort 
  :: MetaOrObject level 
  => Sort level
placeholderSort =
  SortVariableSort $ SortVariable 
    { getSortVariable = noLocationId "S" } --FIXME

--should never appear in output of 'mk' funcs
fixmeSort 
  :: MetaOrObject level 
  => Sort level
fixmeSort =
  SortVariableSort $ SortVariable 
    { getSortVariable = noLocationId "FIXME" } --FIXME
