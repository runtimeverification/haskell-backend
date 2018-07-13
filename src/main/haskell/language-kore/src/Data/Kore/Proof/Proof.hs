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
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE NoMonomorphismRestriction #-}



module Data.Kore.Proof.Proof where

import           Data.Maybe
import           Data.Reflection
import           Data.Fix
import           Data.Foldable
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import           Data.Fix
import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.IndexedModule.MetadataTools


import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.ASTUtils.Substitution

import           GHC.Generics (Generic)
import           Data.Hashable


type Term = CommonPurePattern Object
type Var = Variable Object

data PropF formula rules subproof
  = ByF
  { conclusion    :: formula
  , justification :: rules subproof
  , assumptions   :: S.Set formula
  }
  deriving(Functor, Foldable, Traversable, Show, Generic)

type Prop formula rules = Fix (PropF formula rules)

pattern By conclusion justification assumptions = 
  Fix (ByF conclusion justification assumptions)

type Path = [Int]
type Proof = Prop Term LargeRule

instance (Hashable formula, Hashable (rules subproof))
  => Hashable (PropF formula rules subproof) where 
  hashWithSalt s (ByF a b c) = 
    s `hashWithSalt` a `hashWithSalt` b `hashWithSalt` S.toList c 

instance Hashable Proof where 
    hashWithSalt s (By a b c) = 
        s `hashWithSalt` a `hashWithSalt` b `hashWithSalt` S.toList c 

data LargeRule subproof
 = Assumption Term
 | Discharge Term subproof 
 | Abstract Var subproof
 | ForallElim Term subproof
 | AndIntro subproof subproof
 | AndElimL subproof
 | AndElimR subproof
 | OrIntroL subproof Term 
 | OrIntroR Term     subproof
 -- | OrElim (a \/ b) (C assuming a) (C assuming b)
 | OrElim subproof subproof subproof
 | TopIntro 
 | ExistsIntro Var Term subproof
 -- | ExistsElim (E x. p[x]) (C assuming p[y])
 | ExistsElim subproof Var Term subproof
 | ModusPonens subproof subproof
 -- (\forall x. phi) /\ (\exists y. phi' = y) -> phi[phi'/x]
 -- FunctionalSubst x phi y phi'
 | FunctionalSubst Var Term Var Term
 -- | \exists y . x = y
 -- FunctionalVar x y 
 | FunctionalVar Var Var
 | EqualityIntro Term 
 -- | Path points to the _subtree_ of phi in which the substitution
 -- is to be applied at every possible point.
 -- This is technically less flexible than specifying every position of "x"
 -- But it's good enough for all practical purposes. 
 -- phi_1 = phi_2 /\ phi[phi_1/x] -> phi[phi_2/x]
 -- EqualityElim phi_1 phi_2 phi [path]
 | EqualityElim Term Term Term Path
 -- | NOTE: Should probably rewrite axiom 8 to \forall x. x \in phi = \phi
 -- This should be exactly equivalent, and it fits the other axioms better.
 -- (\forall x . x \in phi) = phi
 | MembershipForall Var Term
 -- | x \in y = (x = y)
 | MembershipEq Var Var 
 -- | x \in \not phi = \not (x \in phi)
 | MembershipNot Var Term 
 -- | (x \in phi_1 /\ phi_2) = (x \in phi_1) /\ (x \in phi_2)
 | MembershipAnd Var Term Term 
 -- | (x \in exists y . phi) = exists y . (x \in phi)
 | MembershipExists Var Var Term
 -- | x \in \sigma(phi_1,...,phi_i,...,phi_n) 
 -- = 
 -- \exists y . (y \in \phi_i /\ x \in \sigma(phi_1,...,y,...,phi_n))
 -- MembershipCong x y i (\sigma(...))
 | MembershipCong Var Var Int Term
 deriving(Show, Functor, Foldable, Generic)


instance Hashable subproof => Hashable (LargeRule subproof)

assume :: Term -> Proof 
assume formula = By formula (Assumption formula) (S.singleton formula)

implies 
    :: Given (MetadataTools Object) 
    => Term -> Term -> Term
implies a b = Fix $ ImpliesPattern $ Implies flexibleSort a b

discharge
    :: Given (MetadataTools Object) 
    => Term -> Proof -> Proof
discharge hypothesis prop@(By conclusion justification assumptions)
   = By 
    (implies hypothesis conclusion) 
    (Discharge hypothesis prop) 
    (S.delete hypothesis assumptions)

useRule
  :: Given (MetadataTools Object) 
  => LargeRule Proof
  -> Proof
useRule (Assumption formula) 
 = assume formula
useRule (Discharge hypothesis conclusion) 
 = discharge hypothesis conclusion
useRule (Abstract var conclusion)
 | elem var (getFreeVars conclusion) = abstract var conclusion
 | otherwise = error $ "Variable " ++ show var ++ " appears in assumptions."
useRule (ExistsElim producer var property (Fix consumer)) = 
    case getConclusion producer of 
      Exists_ _ v p
       | p == property -> Fix consumer 
            { assumptions = S.delete property $ assumptions consumer
            }
       | otherwise -> error "The impossible happened."
      _ -> error "The impossible happened."
useRule rule@(OrElim disjunct left right)
  | getConclusion left == getConclusion right -- FIXME: too picky ==?
     = let Or_ _ leftAssumption rightAssumption = getConclusion disjunct
       in By 
          (getConclusion left)
          rule
          (S.union 
           (S.delete leftAssumption  $ assumptions $ unFix left)
           (S.delete rightAssumption $ assumptions $ unFix right)
          ) 
  | otherwise = error "The impossible happened"
useRule rule = 
  By 
  (interpretRule rule)
  rule
  (S.unions $ map (assumptions . unFix) $ toList rule)

interpretRule
  :: Given (MetadataTools Object)
  => LargeRule Proof 
  -> Term 
interpretRule (ModusPonens a b) = 
  let (Implies_ _ a' b') = getConclusion b 
  in if a' == getConclusion a 
    then b' 
    else error 
      $ "Can't match \n" 
      ++ prettyPrintToString a' 
      ++ "\n with \n" 
      ++ prettyPrintToString (getConclusion a)
      ++ "in ModusPonens"
  -- Default equality too strong? Probably. 
interpretRule (FunctionalSubst x phi y phi') = 
  ((mkForall x phi) `mkAnd` (mkExists y (phi' `mkEquals` Var_ y))) 
  `mkImplies` 
  (subst (Var_ x) phi' phi)
interpretRule (FunctionalVar x y) = mkExists y (Var_ x `mkEquals` Var_ y)
interpretRule (EqualityIntro a) = mkEquals a a
interpretRule (EqualityElim phi1 phi2 phi path) =
  (phi1 `mkEquals` phi2) 
  `mkImplies` (
      phi
      `mkImplies` 
      (localInPattern path (subst phi1 phi2) phi)
  )
interpretRule (MembershipForall x phi) = 
  (mkForall x (Var_ x `mkIn` phi)) `mkEquals` phi
interpretRule (MembershipEq x y) = 
  (Var_ x `mkIn` Var_ y)
  `mkEquals`
  (Var_ x `mkEquals` Var_ y)
interpretRule (MembershipNot x phi) = 
  (Var_ x `mkIn` (mkNot phi))
  `mkEquals`
  (mkNot (Var_ x `mkIn` phi))
interpretRule (MembershipAnd x phi1 phi2) = 
  (Var_ x `mkIn` (phi1 `mkAnd` phi2))
  `mkEquals`
  ((Var_ x `mkIn` phi1) `mkAnd` (Var_ x `mkIn` phi2))
interpretRule (MembershipExists x y phi) = 
  (Var_ x `mkIn` (mkExists y phi))
  `mkEquals`
  (mkExists y (Var_ x `mkIn` phi))
interpretRule (MembershipCong x y i phi) = 
  (Var_ x `mkIn` phi)
  `mkEquals`
  (mkExists y $ (Var_ y `mkIn` phi_i) `mkAnd` (Var_ x `mkIn` phi'))
    where phi'       = phi & inPath [i] .~ (Var_ y)
          Just phi_i = phi ^? inPath [i]
interpretRule (AndIntro a b) = mkAnd (getConclusion a) (getConclusion b)
interpretRule (AndElimL a) = fromJust $ getConclusion a ^? inPath [0]
interpretRule (AndElimR a) = fromJust $ getConclusion a ^? inPath [1]
interpretRule (ExistsIntro var term property) = 
    mkExists var $ subst (Var_ var) term $ getConclusion property
interpretRule (OrIntroL a b) = mkOr (getConclusion a) b 
interpretRule (OrIntroR a b) = mkOr a (getConclusion b)
interpretRule (ForallElim term proof) = case getConclusion proof of 
    Forall_ s v p -> subst (Var_ v) term p 

getConclusion = conclusion . unFix

abstract 
    :: Given (MetadataTools Object) 
    => Var -> Proof -> Proof
abstract var prop@(By conclusion justification assumptions)
  | elem var $ getFreeVars prop
    = error $ "Variable " 
            ++ show var 
            ++ "appears in assumptions" 
            ++ show assumptions
  | otherwise  
    = Fix $ (unFix prop) {
        conclusion = mkForall var conclusion
      }

getFreeVars :: Proof -> S.Set Var
getFreeVars proof = 
    S.unions 
  $ map freeVars 
  $ S.toList 
  $ assumptions
  $ unFix proof 
