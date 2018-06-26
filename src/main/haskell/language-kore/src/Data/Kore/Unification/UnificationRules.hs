{-|
Module      : Data.Kore.Unification.UnificationRules
Description : Inference rules underlying unificatoin
              Should desugar to ML axioms, but this
              will all be replaced anyway. 
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
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-orphans        #-}


module Data.Kore.Unification.UnificationRules where

import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix
import           Control.Monad.State


import           Data.Kore.AST.Common                     
import           Data.Kore.AST.PureML                     ( CommonPurePattern
                                                          )
import           Data.Kore.AST.MLPatterns                 ( getPatternResultSort
                                                          )
import           Data.Kore.AST.MetaOrObject               ( MetaOrObject
                                                          )
import           Data.Kore.Proof.ProofSystemWithHypos     ( Proof
                                                          , ProofSystem(..) 
                                                          , ProofLine(..) 
                                                          , Formula(..)
                                                          , Rules(..)
                                                          , Indexing(..) 
                                                          , claim 
                                                          , justification
                                                          , assumptions
                                                          , lookupLine
                                                          , makeRule1
                                                          , makeRule2
                                                          )
import           Data.Kore.IndexedModule.MetadataTools    ( MetadataTools
                                                          , getResultSort
                                                          )

data UnificationRules level ix
  = Assumption
  | Discharge !ix !ix
  | EqSymmetric !ix -- (a = b) => (b = a)
  | Refl (Term level) 
  | Substitution !ix !ix --ix2[LHS of ix1 \ RHS of ix2]
  | LocalSubstitution !ix !ix !Path
  | NoConfusion !ix -- result is a conjunction
  | AndIntro !ix !ix 
  | AndL !ix -- a /\ b => a
  | AndR !ix 
  | ModusPonens !ix !ix
  | IffIntro !ix !ix
  | IffRight !ix 
  | IffLeft !ix 
  | Prop5243 !ix -- t1 /\ t2 <-> t1 /\ (t1 = t2)
  deriving(Functor, Foldable, Traversable, Show)

type Term level = CommonPurePattern level
type Idx = Int
type Path  = [Int]
type ProofState level 
  = State (Proof Int (UnificationRules level) (Term level))

instance Indexing Int where 
  zeroIx = 0
  nextIx = (+1)

instance MetaOrObject level 
  => Rules (UnificationRules level) where
  assumption = Assumption
  elim = Discharge

instance MetaOrObject level 
  => Formula (Term level) where
  implies a b = Fix $ ImpliesPattern $ Implies
    { impliesSort = placeholderSort
    , impliesFirst = a 
    , impliesSecond = b
    }

placeholderSort 
  :: MetaOrObject level 
  => Sort level
placeholderSort =
  SortVariableSort $ SortVariable 
    { getSortVariable = noLocationId "S" } --FIXME

instance MetaOrObject level 
  => ProofSystem Int (UnificationRules level) (Term level) where 
  
pattern Equation
  :: Sort level
     -> Sort level
     -> Fix (Pattern level variable)
     -> Fix (Pattern level variable)
     -> Fix (Pattern level variable)
pattern Equation s1 s2 a b = 
  Fix (EqualsPattern (Equals s1 s2 a b))

flipEqn
  :: MetaOrObject level 
  => CommonPurePattern level 
  -> CommonPurePattern level 
flipEqn (Equation s1 s2 a b) = Equation s1 s2 b a
flipEqn _ = error "Input should be Equation"

applySymmetry 
  :: MetaOrObject level 
  => Idx 
  -> ProofState level Idx
applySymmetry = makeRule1 flipEqn EqSymmetric

applyIffIntro
  :: MetaOrObject level
  => Idx
  -> Idx 
  -> ProofState level Idx
applyIffIntro = makeRule2 makeIff IffIntro 

makeIff 
  :: MetaOrObject level
  => Term level -> Term level -> Term level
makeIff (Fix (ImpliesPattern (Implies s1 a b))) _ = Fix (IffPattern (Iff s1 a b))
makeIff _ _ = error "Input should be ImpliesPattern"

-- | Given term a, returns index of newly proved statement (a=a)
applyRefl
  :: MetaOrObject level
  => MetadataTools level
  -> Term level
  -> ProofState level Idx
applyRefl tools term = do
  addLine ProofLine
    { claim = Equation (getSort tools term) (getSort tools term) term term 
    , justification = Refl term
    , assumptions = S.empty
    }

getLHS
  :: MetaOrObject level 
  => Term level 
  -> Term level 
getLHS (Equation s1 s2 a b) = a
getLHS _ = error "Input should be Equation"

getRHS
  :: MetaOrObject level 
  => Term level 
  -> Term level 
getRHS (Equation s1 s2 a b) = b
getRHS _ = error "Input should be Equation"

lhsIsVariable
  :: MetaOrObject level
  => CommonPurePattern level 
  -> Bool
lhsIsVariable (Equation s1 s2 a b) = 
  case a of
    Fix (VariablePattern _) -> True
    _ -> False
lhsIsVariable _ = error "Input should be Equation"

-- | Given pattern (a=b) and C[a], returns C[b]
subst
  :: MetaOrObject level 
  => CommonPurePattern level 
  -> CommonPurePattern level 
  -> CommonPurePattern level
subst eqn@(Equation s1 s2 a b) pat =
  if pat == a then b else Fix $ fmap (subst eqn) $ unFix pat
subst _ _ = error "Input should be Equation"

-- | apply a transformation locally, at position given by the path
-- TODO: Make this a lens. 
localInPattern 
   :: MetaOrObject level 
   => Path 
   -> (CommonPurePattern level -> CommonPurePattern level)
   -> CommonPurePattern level 
   -> CommonPurePattern level 
localInPattern []     f pat = f pat
localInPattern (n:ns) f pat = Fix $
  case unFix pat of
    AndPattern (And s1 a b) 
      -> AndPattern $ case n of 
           0 -> And s1 (localInPattern ns f a) b
           1 -> And s1 a (localInPattern ns f b)
           m -> error ("No " ++ show m ++ " position")
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
           m -> error ("No " ++ show m ++ " position")
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
           m -> error ("No " ++ show m ++ " position")
    ImpliesPattern (Implies s1 a b)
      -> ImpliesPattern $ case n of 
          0 -> Implies s1 (localInPattern ns f a) b
          1 -> Implies s1 a (localInPattern ns f b)
          m -> error ("No " ++ show m ++ " position")
    InPattern (In s1 s2 a b)
      -> InPattern $ case n of 
           0 -> In s1 s2 (localInPattern ns f a) b 
           1 -> In s1 s2 a (localInPattern ns f b)
           m -> error ("No " ++ show m ++ " position")
    NextPattern (Next s1 a)
      -> NextPattern $ Next s1 (localInPattern ns f a)
    NotPattern (Not s1 a)
      -> NotPattern $ Not s1 (localInPattern ns f a)
    OrPattern (Or s1 a b)
      -> OrPattern $ case n of 
           0 -> Or s1 (localInPattern ns f a) b 
           1 -> Or s1 a (localInPattern ns f b)
           m -> error ("No " ++ show m ++ " position")
    RewritesPattern (Rewrites s1 a b)
      -> RewritesPattern $ case n of 
           0 -> Rewrites s1 (localInPattern ns f a) b 
           1 -> Rewrites s1 a (localInPattern ns f b)
           m -> error ("No " ++ show m ++ " position")
    _ -> error "FIXME: Add more constructors here"

-- | applyLocalSubstitution with path [] takes index of statement (a=b) 
-- and index of a statement P[a]
-- and returns index of newly proved P[b]
-- If the path is nontrivial, it only substitutes a for b in the subterm
-- given by the path. 
applyLocalSubstitution
  :: MetaOrObject level 
  => Idx
  -> Idx 
  -> Path 
  -> State (Proof Int (UnificationRules level) (Term level)) Int
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

isTrivial 
  :: MetaOrObject level
  => CommonPurePattern level 
  -> Bool
isTrivial (Equation s1 s2 a b) = (a == b)
isTrivial _ = error "Input should be Equation"

-- | applyNoConfusion takes index of a statement like C(a,b)=C(x,y)
-- and returns index of newly proved statement (a=x)/\(b=y)
-- Assumes constructor heads of LHS and RHS match.
applyNoConfusion
  :: MetaOrObject level
  => MetadataTools level 
  -> Idx
  -> ProofState level Int
applyNoConfusion tools = makeRule1 (splitConstructor tools) NoConfusion

-- | splitConstructor takes an eqn pattern C(a,b)=C(x,y) to (a=x)/\(b=y)
-- Assumes constructor heads of LHS and RHS match.
splitConstructor 
  :: MetaOrObject level
  => MetadataTools level 
  -> CommonPurePattern level 
  -> CommonPurePattern level
splitConstructor tools (Equation s1 s2 a b) = 
  let ApplicationPattern (Application _ aChildren) = unFix a
      ApplicationPattern (Application _ bChildren) = unFix b
  in if length aChildren == 0
  then undefined -- "True"
  else 
    foldr1 (makeAnd tools) $
    zipWith 
      (\ac bc -> 
        Equation (getSort tools ac) 
        s2 
        ac 
        bc
      ) 
      aChildren 
      bChildren 
splitConstructor _ _ = error "Input should be Equation"

getSort 
  :: MetaOrObject level 
  => MetadataTools level 
  -> CommonPurePattern level
  -> Sort level
getSort tools x = (getPatternResultSort (getResultSort tools) $ unFix x)

-- | applyAndL takes the index of a statement a /\ b
-- and returns index of newly proved statement a
applyAndL
  :: MetaOrObject level
  => Int 
  -> ProofState level Int
applyAndL = makeRule1 getAndL AndL

-- | applyAndR takes the index of a statement a /\ b
-- and returns index of newly proved statement b
applyAndR
  :: MetaOrObject level
  => Int 
  -> ProofState level Int
applyAndR = makeRule1 getAndR AndR

getAndL :: MetaOrObject level => Term level -> Term level
getAndL (Fix (AndPattern (And _ x _ ))) = x
getAndL _ = error "Argument should be AndPattern"

getAndR :: MetaOrObject level => Term level -> Term level
getAndR (Fix (AndPattern (And _ _ y ))) = y
getAndR _ = error "Argument should be AndPattern"

applyProp5243
  :: MetaOrObject level 
  => MetadataTools level 
  -> Idx 
  -> ProofState level Idx
applyProp5243 tools = makeRule1 (makeProp5243 tools) Prop5243

makeProp5243 
  :: MetaOrObject level 
  => MetadataTools level 
  -> Term level 
  -> Term level 
makeProp5243 tools e = 
  let t1 = getAndL e
      t2 = getAndR e 
      sort = (getSort tools t1)
  in makeIff e (makeAnd tools t1 (Equation sort sort t1 t2))


-- | applyAndIntro takes the indices of two statements a and b
-- and returns the index of newly proved statement a /\ b 
applyAndIntro
  :: MetaOrObject level
  => MetadataTools level
  -> Int
  -> Int 
  -> ProofState level Int
applyAndIntro tools = makeRule2 (makeAnd tools) AndIntro


-- | makeAnd a b = a /\ b
makeAnd 
  :: MetaOrObject level
  => MetadataTools level
  -> Term level
  -> Term level
  -> Term level
makeAnd tools a b = Fix $ AndPattern $ And 
  { andSort = getSort tools a
  , andFirst = a
  , andSecond = b
  }

-- | makeConjunction [a, b, c] = a /\ (b /\ c)
makeConjunction
  :: MetaOrObject level
  => MetadataTools level 
  -> [Idx]
  -> ProofState level Idx
makeConjunction tools [ix] = return ix
makeConjunction tools (ix : ixs) = do
  ix' <- makeConjunction tools ixs 
  applyAndIntro tools ix ix' 
makeConjunction tools [] = error "FIXME: all this should be replaced anyway"

splitConjunction
  :: MetaOrObject level 
  => Idx 
  -> ProofState level (S.Set Idx)
splitConjunction ix = do
  eqn <- claim <$> lookupLine ix
  if isConjunction eqn
  then do
    ixLeft  <- applyAndL ix
    ixRight <- applyAndR ix
    splitResultLeft  <- splitConjunction ixLeft 
    splitResultRight <- splitConjunction ixRight 
    return $ S.union splitResultLeft splitResultRight
  else return $ S.singleton ix

isConjunction
  :: MetaOrObject level 
  => Term level
  -> Bool
isConjunction (Fix (AndPattern _)) = True
isConjunction _                    = False



