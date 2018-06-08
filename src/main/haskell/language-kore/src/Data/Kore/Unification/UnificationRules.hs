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
  deriving(Functor, Foldable, Traversable)

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

applyCommutativity 
  :: Int 
  -> State (Proof Int UnificationRules Term) Int
applyCommutativity = makeRule1 flipEqn EqSymmetric

lhsIsVariable (Equation s1 s2 a b) = 
  case a of
    Fix (VariablePattern _) -> True
    _ -> False

subst (Equation s1 s2 a b) p2 = cata $
  \pat -> if pat == unFix a then b else Fix pat

a = Fix $ VariablePattern $ Variable (noLocationId "a") placeholderSort 
b = Fix $ VariablePattern $ Variable (noLocationId "b") placeholderSort 
c = Fix $ VariablePattern $ Variable (noLocationId "c") placeholderSort 

aEqb :: Term
aEqb = Fix $ EqualsPattern $ Equals placeholderSort placeholderSort a b 

bEqc :: Term
bEqc = Fix $ EqualsPattern $ Equals placeholderSort placeholderSort b c 

-- pattern VarEquation s1 s2 s3 a b = 
--   Fix (EqualsPattern (Equals s1 s2 (
--     Fix (VariablePattern
--       (Variable a s3) --FIXME: we have always s1 == s3!!! annoying!!
--       )
--     ) b
--   ))

-- pattern FlippedVarEquation s1 s2 s3 a b = 
--   Fix (EqualsPattern (Equals s1 s2 a (
--     Fix (VariablePattern
--       (Variable b s3) 
--       )
--   )))
-- class 
--   ( Indexing ix
--   , Rules rule
--   , Formula formula) 
--   => ProofSystem ix rule formula where 

--   getNextIx :: State (Proof ix rule formula) ix
--   getNextIx = do 
--     maxIx <- M.lookupMax <$> get
--     return $ case maxIx of 
--       Just (ix,_) -> nextIx ix 
--       Nothing     -> zeroIx

--   assume :: formula -> State (Proof ix rule formula) ix
--   assume formula = do
--     ix <- getNextIx
--     let line = ProofLine
--           { claim = formula
--           , justification = assumption
--           , assumptions = S.singleton ix
--           }
--     modify $ M.insert ix line
--     return ix

--   discharge :: ix -> ix -> State (Proof ix rule formula) ix
--   discharge ix1 ix2 = do
--     Just hypothesis <- M.lookup ix1 <$> get
--     Just conclusion <- M.lookup ix2 <$> get
--     let line = ProofLine
--           { claim = implies (claim hypothesis) (claim conclusion)
--           , justification = elim ix1 ix2
--           , assumptions = S.delete ix1 $ assumptions conclusion
--           }
--     addLine line

--   addLine :: ProofLine ix rule formula -> State (Proof ix rule formula) ix
--   addLine line = do
--     ix <- getNextIx
--     modify $ M.insert ix line
--     return ix

  

  -- Can also deal with quantifiers:
  
  -- forall :: var -> formula -> var
  -- abs :: var -> ix -> rule ix

  -- abstract :: var -> ix -> State (Proof ix rule formula) ix

  -- etc



