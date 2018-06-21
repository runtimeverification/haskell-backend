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
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE BangPatterns           #-}

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
  | Discharge !ix !ix
  | EqSymmetric !ix -- (a = b) => (b = a)
  | Refl Term 
  | Substitution !ix !ix --ix2[LHS of ix1 \ RHS of ix2]
  | LocalSubstitution !ix !ix !Path
  | NoConfusion !ix -- result is a conjunction
  | AndIntro !ix !ix 
  | AndL !ix -- a /\ b => a
  | AndR !ix 
  | ModusPonens !ix !ix
  | IffIntro !ix !ix
  deriving(Functor, Foldable, Traversable, Show)

type Term  = CommonPurePattern Meta
type Idx = Int
type Path  = [Int]

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
  :: Idx 
  -> State (Proof Int UnificationRules Term) Idx
applySymmetry = makeRule1 flipEqn EqSymmetric

applyIffIntro
  :: Idx
  -> Idx 
  -> State (Proof Int UnificationRules Term) Idx
applyIffIntro = makeRule2 iffIntro IffIntro 

iffIntro :: Term -> Term -> Term
iffIntro (Fix (ImpliesPattern (Implies s1 a b))) _ = Fix (IffPattern (Iff s1 a b))

applyRefl
  :: Term 
  -> State (Proof Int UnificationRules Term) Idx
applyRefl term = do
  addLine ProofLine
    { claim = Equation placeholderSort placeholderSort term term 
    , justification = Refl term
    , assumptions = S.empty
    }

getLHS (Equation s1 s2 a b) = a
getRHS (Equation s1 s2 a b) = b

lhsIsVariable (Equation s1 s2 a b) = 
  case a of
    Fix (VariablePattern _) -> True
    _ -> False

subst eqn@(Equation s1 s2 a b) pat =
  if pat == a then b else Fix $ fmap (subst eqn) $ unFix pat

localInPattern []     f pat = f pat
localInPattern (n:ns) f pat = Fix $
  case unFix pat of
    AndPattern (And s1 a b) 
      -> AndPattern $ case n of 
           0 -> And s1 (localInPattern ns f a) b
           1 -> And s1 a (localInPattern ns f b)
    ApplicationPattern (Application head children)
      -> let (a, b : bs) = splitAt n children 
             children'   = a ++ [localInPattern ns f b] ++ bs 
         in ApplicationPattern (Application head $ children')
    CeilPattern (Ceil s1 s2 a) 
      -> CeilPattern $ Ceil s1 s2 (localInPattern ns f a)
    DomainValuePattern (DomainValue s1 a) 
      -> DomainValuePattern $ DomainValue s1 (localInPattern ns f a)
    EqualsPattern (Equals s1 s2 a b)
      -> EqualsPattern $ case n of 
           0 -> Equals s1 s2 (localInPattern ns f a) b 
           1 -> Equals s1 s2 a (localInPattern ns f b)
    ExistsPattern (Exists s1 v a) 
      -> ExistsPattern $ Exists s1 v (localInPattern ns f a)
    FloorPattern (Floor s1 s2 a)
      -> FloorPattern $ Floor s1 s2 (localInPattern ns f a)
    ForallPattern (Forall s1 v a)
      -> ForallPattern $ Forall s1 v (localInPattern ns f a)
    IffPattern (Iff s1 a b)
      -> IffPattern $ case n of 
           0 -> Iff s1 (localInPattern ns f a) b 
           1 -> Iff s1 a (localInPattern ns f b)
    ImpliesPattern (Implies s1 a b)
      -> ImpliesPattern $ case n of 
          0 -> Implies s1 (localInPattern ns f a) b
          1 -> Implies s1 a (localInPattern ns f b)
    InPattern (In s1 s2 a b)
      -> InPattern $ case n of 
           0 -> In s1 s2 (localInPattern ns f a) b 
           1 -> In s1 s2 a (localInPattern ns f b)
    NextPattern (Next s1 a)
      -> NextPattern $ Next s1 (localInPattern ns f a)
    NotPattern (Not s1 a)
      -> NotPattern $ Not s1 (localInPattern ns f a)
    OrPattern (Or s1 a b)
      -> OrPattern $ case n of 
           0 -> Or s1 (localInPattern ns f a) b 
           1 -> Or s1 a (localInPattern ns f b)
    RewritesPattern (Rewrites s1 a b)
      -> RewritesPattern $ case n of 
           0 -> Rewrites s1 (localInPattern ns f a) b 
           1 -> Rewrites s1 a (localInPattern ns f b)



-- applySubstitution
--   :: Int
--   -> Int
--   -> State (Proof Int UnificationRules Term) Int
-- -- applySubstitution = makeRule2 subst Substitution
-- applySubstitution ix1 ix2 = do
--   Just line1 <- M.lookup ix1 <$> get
--   Just line2 <- M.lookup ix2 <$> get
--   let substitutedClaim2 = subst (claim line1) (claim line2)
--   if substitutedClaim2 == claim line2 -- substitution was a noop
--   then return ix2 
--   else addLine ProofLine 
--     { claim = substitutedClaim2
--     , justification = Substitution ix1 ix2
--     , assumptions = S.unions [assumptions line1, assumptions line2]
--     }

applyLocalSubstitution
  :: Idx
  -> Idx 
  -> Path 
  -> State (Proof Int UnificationRules Term) Int
applyLocalSubstitution ix1 ix2 path = do 
  Just line1 <- M.lookup ix1 <$> get
  Just line2 <- M.lookup ix2 <$> get 
  let substitutedClaim2 = localInPattern path (subst (claim line1)) (claim line2)
  if substitutedClaim2 == claim line2 -- substitution was a noop
  then return ix2 
  else addLine ProofLine 
    { claim = substitutedClaim2
    , justification = LocalSubstitution ix1 ix2 path
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

applyAndIntro
  :: Int
  -> Int 
  -> State (Proof Int UnificationRules Term) Int
applyAndIntro = makeRule2 makeAnd AndIntro
makeAnd 
  :: Term
  -> Term
  -> Term
makeAnd a b = Fix $ AndPattern $ And 
  { andSort = placeholderSort
  , andFirst = a
  , andSecond = b
  }

conj a b = Fix $ AndPattern $ And 
  { andSort = placeholderSort
  , andFirst = a 
  , andSecond = b
  }

isConjunction (Fix (AndPattern _)) = True
isConjunction _                    = False



