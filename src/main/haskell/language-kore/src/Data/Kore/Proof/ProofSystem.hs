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

data PropF formula rules subproof
  = ByF
  { conclusion :: formula
  , justification :: Maybe (rules subproof)
  }
  deriving(Functor, Foldable, Traversable)

type Prop formula rules = Fix (PropF formula rules)

pattern By conclusion justification = Fix (ByF conclusion justification)

type Path = [Int]

data LargeRules subproof
 = Tautology 

class Ord variable 
  => HasFreeVars formula variable | formula -> variable where 
  getFreeVars :: formula -> S.Set variable

class (Foldable rules, Functor rules, Ord formula) 
  => ProofSystem formula rules where 


  useRule 
    :: rules (Prop formula rules) 
    -> Prop formula rules

  freeVars 
    :: HasFreeVars formula variable
    => Prop formula rules 
    -> S.Set variable
  freeVars = S.unions . toList . S.map getFreeVars . freeHypotheses

  freeHypotheses 
    :: (Functor rules, Foldable rules, Ord formula) 
    => Prop formula rules 
    -> S.Set formula

  freeHypotheses (By a Nothing) = S.singleton a
  freeHypotheses (By a (Just rule)) = 
   S.unions $ map freeHypotheses $ toList rule

  

