{-|
Module      : Data.Kore.Unification.UnifierImpl
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
import           Data.Kore.Proof.SmartConstructors
import           Data.Kore.Proof.Substitution


type Term = CommonPurePattern Object
type Var = Variable Object

data PropF formula rules subproof
  = ByF
  { conclusion    :: formula
  , justification :: rules subproof
  , assumptions   :: S.Set formula
  }
  deriving(Functor, Foldable, Traversable)

type Prop formula rules = Fix (PropF formula rules)

pattern By conclusion justification assumptions = 
  Fix (ByF conclusion justification assumptions)

type Path = [Int]
type Proof = Prop Term LargeRule

data LargeRule subproof
 = Assumption Term
 | Discharge Term subproof 
 | Abstract Var subproof
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
 deriving(Show,Functor,Foldable)


assume :: Term -> Proof 
assume formula = By formula (Assumption formula) (S.singleton formula)

implies :: Term -> Term -> Term
implies a b = Fix $ ImpliesPattern $ Implies placeholderSort a b

discharge :: Term -> Proof -> Proof
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
  let (Implies_ _ a' b') = conclusion $ unFix b 
  in b'
interpretRule (FunctionalSubst x phi y phi') = 
  ((mkForall x phi) `mkAnd` (mkExists y (phi' `mkEquals` Var_ y))) 
  `mkImplies` 
  (subst (Var_ x) phi' phi)
interpretRule (FunctionalVar x y) = mkExists y (Var_ x `mkEquals` Var_ y)
interpretRule (EqualityIntro a) = mkEquals a a
interpretRule (EqualityElim phi1 phi2 phi path) =
  ((phi1 `mkEquals` phi2) `mkAnd` phi) 
  `mkImplies` 
  (localInPattern path (subst phi1 phi2) phi)
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
    where phi'  = phi & childIx i .~ (Var_ y)
          phi_i = fromJust $ phi ^? childIx i


abstract :: Var -> Proof -> Proof
abstract var prop@(By conclusion justification assumptions)
 = Fix $ (unFix prop) {
    conclusion = Fix $ ForallPattern $ Forall placeholderSort var conclusion
    }

getFreeVars :: Proof -> S.Set Var
getFreeVars = undefined

-- useRule 
--   :: rules (Prop formula rules) 
--   -> Prop formula rules 
-- useRule rule = By
--   (ruleToFormula rule)
--   rule 
--   (S.unions $ map (assumptions . unFix) $ toList rule)

-- freeVars 
--   :: HasFreeVars formula variable
--   => Prop formula rules 
--   -> S.Set variable
-- freeVars = S.unions . map getFreeVars . toList . assumptions . unFix

-- byAbstraction 
--   :: variable 
--   -> Prop formula rules 
--   -> rules (Prop formula rules)

-- abstract 
--   :: (HasFreeVars formula variable, Show variable)
--   => variable 
--   -> Prop formula rules 
--   -> Prop formula rules 
-- abstract var prop@(By conclusion justification assumptions)
--   | not (elem var $ freeVars prop) = By 
--     (forall var conclusion)
--     (byAbstraction var prop)
--     (assumptions)
--   | otherwise = error $ "variable " ++ show var ++ " appears in assumptions"
  
