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


module Data.Kore.Proof.ProofSystem where

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

import           Data.Kore.ASTPrettyPrint

-- I wanted to use Fix, abstract over formula, variable types etc
-- but for now it's more trouble than it's worth
-- especially since with ML patterns you need to look up
-- sort information to construct predicates. 

-- data PropF formula rules subproof
--   = ByF
--   { conclusion    :: formula
--   , justification :: rules subproof
--   , assumptions   :: S.Set formula
--   }
--   deriving(Functor, Foldable, Traversable)

-- type Prop formula rules = Fix (PropF formula rules)

-- pattern By conclusion justification assumptions = 
--   Fix (ByF conclusion justification assumptions)

-- type Path = [Int]

-- data LargeRules subproof
--  = Tautology 

-- class (Eq variable, Ord variable)
--   => HasFreeVars formula variable | formula -> variable where 
--   getFreeVars :: formula -> S.Set variable

-- class Ord formula => Formula formula where 
--   implies :: formula -> formula -> formula
--   forall :: HasFreeVars formula variable => variable -> formula -> formula

-- class (Foldable rules, Functor rules) => Rules rules where 

-- class (Formula formula, Rules rules) 
--   => ProofSystem formula rules | formula -> rules where 

--   byAssumption :: formula -> rules (Prop formula rules)
 
--   assume :: formula -> Prop formula rules 
--   assume formula = By formula (byAssumption formula) (S.singleton formula)

--   discharging :: formula -> Prop formula rules -> rules (Prop formula rules)

--   discharge :: formula -> Prop formula rules -> Prop formula rules
--   discharge hypothesis prop@(By conclusion justification assumptions)
--     = By 
--     (implies hypothesis conclusion) 
--     (discharging hypothesis prop) 
--     (S.delete hypothesis assumptions)

--   ruleToFormula
--     :: rules (Prop formula rules)
--     -> formula

--   useRule 
--     :: rules (Prop formula rules) 
--     -> Prop formula rules 
--   useRule rule = By
--     (ruleToFormula rule)
--     rule 
--     (S.unions $ map (assumptions . unFix) $ toList rule)

--   freeVars 
--     :: HasFreeVars formula variable
--     => Prop formula rules 
--     -> S.Set variable
--   freeVars = S.unions . map getFreeVars . toList . assumptions . unFix

--   byAbstraction 
--     :: variable 
--     -> Prop formula rules 
--     -> rules (Prop formula rules)

--   abstract 
--     :: (HasFreeVars formula variable, Show variable)
--     => variable 
--     -> Prop formula rules 
--     -> Prop formula rules 
--   abstract var prop@(By conclusion justification assumptions)
--     | not (elem var $ freeVars prop) = By 
--       (forall var conclusion)
--       (byAbstraction var prop)
--       (assumptions)
--     | otherwise = error $ "variable " ++ show var ++ " appears in assumptions"
  

