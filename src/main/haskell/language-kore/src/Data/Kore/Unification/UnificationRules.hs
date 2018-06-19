{-|
Module      : Data.Kore.Unification.UnifierImpl
Description : Datastructures and functionality for performing unification on
              Pure patterns
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
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE DeriveTraversable      #-}
{-# LANGUAGE PatternSynonyms        #-}
{-# LANGUAGE FlexibleContexts       #-}

module Data.Kore.Unification.UnificationRules where

import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix
import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.PureML
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Unification.ProofSystemWithHypos
import           Data.Kore.Unparser.Unparse
data UnificationRules ix
  = Assumption
  | Discharge ix ix
  | EqSymmetric ix -- (a = b) => (b = a)
  | Substitution ix ix --ix2[LHS of ix1 \ RHS of ix2]
  | NoConfusion ix -- result is a conjunction
  | AndL ix -- a /\ b => a
  | AndR ix 
  deriving(Functor, Foldable, Traversable, Show)

type Term = CommonPurePattern Meta

instance Indexing Int where 
  zeroIx = 0
  nextIx = (+1)

instance Rules UnificationRules where
  assumption = Assumption
  elim = Discharge

instance Formula Term where
  implies a b = Fix $ ImpliesPattern $ Implies
    { impliesSort = placeholderSort
    , impliesFirst = a 
    , impliesSecond = b
    }

placeholderSort =
  SortVariableSort $ SortVariable 
    { getSortVariable = noLocationId "S" } --FIXME

instance ProofSystem Int UnificationRules Term where 
  
pattern Equation s1 s2 a b = 
  Fix (EqualsPattern (Equals s1 s2 a b))

flipEqn (Equation s1 s2 a b) = Equation s1 s2 b a

applySymmetry 
  :: Int 
  -> State (Proof Int UnificationRules Term) Int
applySymmetry = makeRule1 flipEqn EqSymmetric

getLHS (Equation s1 s2 a b) = a
getRHS (Equation s1 s2 a b) = b

lhsIsVariable (Equation s1 s2 a b) = 
  case a of
    Fix (VariablePattern _) -> True
    _ -> False

subst eqn@(Equation s1 s2 a b) pat =
  if pat == a then b else Fix $ fmap (subst eqn) $ unFix pat

applySubstitution
  :: Int
  -> Int
  -> State (Proof Int UnificationRules Term) Int
-- applySubstitution = makeRule2 subst Substitution
applySubstitution ix1 ix2 = do
  Just line1 <- M.lookup ix1 <$> get
  Just line2 <- M.lookup ix2 <$> get
  let substitutedClaim2 = subst (claim line1) (claim line2)
  if substitutedClaim2 == claim line2 -- substitution was a noop
  then return ix1 
  else addLine ProofLine 
    { claim = substitutedClaim2
    , justification = Substitution ix1 ix2
    , assumptions = S.unions [assumptions line1, assumptions line2]
    }

isTrivial (Equation s1 s2 a b) = (a == b)

applyNoConfusion
  :: Int 
  -> State (Proof Int UnificationRules Term) Int
applyNoConfusion = makeRule1 splitConstructor NoConfusion

splitConstructor (Equation s1 s2 a b) = 
  let ApplicationPattern (Application _ aChildren) = unFix a
      ApplicationPattern (Application _ bChildren) = unFix b
  in if length aChildren == 0
  then undefined -- "True"
  else 
    foldr1 conj $
    zipWith 
      (\ac bc -> Equation s1 s2 ac bc) 
      aChildren 
      bChildren 

applyAndL
  :: Int 
  -> State (Proof Int UnificationRules Term) Int
applyAndL = makeRule1 getAndL AndL

applyAndR
  :: Int 
  -> State (Proof Int UnificationRules Term) Int
applyAndR = makeRule1 getAndR AndR

getAndL (Fix (AndPattern (And _ x _ ))) = x
getAndR (Fix (AndPattern (And _ _ y ))) = y

conj a b = Fix $ AndPattern $ And 
  { andSort = placeholderSort
  , andFirst = a 
  , andSecond = b
  }

isConjunction (Fix (AndPattern _)) = True
isConjunction _                    = False



