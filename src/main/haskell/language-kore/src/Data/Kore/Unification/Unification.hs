{-|
Module      : Data.Kore.Unification.Unification
Description : Datastructures and functionality for performing unification on
              Pure patterns
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
{-# LANGUAGE 
  FlexibleContexts
, LambdaCase
, DeriveGeneric
#-}
module Data.Kore.Unification.Unification where

import           Data.Kore.AST.Common
import           Data.Kore.AST.MLPatterns
import           Data.Kore.AST.PureML
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.FixTraversals
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.ASTUtils.SmartConstructors 
import           Data.Kore.ASTUtils.Substitution 
import           Data.Kore.Proof.Proof
import           Data.Kore.Proof.Dummy
import           Data.Kore.Proof.Util


import           Control.Monad                         (foldM)
import           Data.Fix
import           Data.Reflection
import           Data.Function                         (on)
import           Data.List                             (groupBy, partition,
                                                        sortBy)
import           Data.Kore.Unparser.Unparse
import           Data.Hashable
import           GHC.Generics (Generic)

import Debug.Trace
import Text.Groom 

spy x = trace (groom x) x 

go :: Given (MetadataTools Object) 
   => [Proof] 
   -> [Proof] 
   -> Either UnificationError Proof
go finished [] = Right $ andIntroN finished
go finished (eq : eqs) = case getConclusion eq of 
    And_ s a b -> go finished $ 
      useRule (AndElimL eq) : useRule (AndElimR eq) : eqs
    Equals_ s1 s2 (Var_ x) b 
      | occursCheck eq -> 
          go (eq : finished) (map (provableSubst eq []) eqs)
      | otherwise -> 
          Left $ OccursCheck eq 
    Equals_ s1 s2 a (Var_ x) -> go finished $ 
      flipEqn eq : eqs
    Equals_ s1 s2 a b -> do 
      eq' <- splitConstructor eq 
      go finished (eq' : eqs)

data UnificationError
  = ConstructorClash Term Term 
  | OccursCheck Proof 
  deriving(Show, Generic)

instance Hashable UnificationError


-- substituting an equation x = t into itself 
-- is a noop iff x \notin FV(t)
occursCheck 
    :: Given (MetadataTools Object)
    => Proof 
    -> Bool
occursCheck eq =
    (getConclusion $ provableSubst eq [1] eq) == getConclusion eq


splitConstructor
    :: Given (MetadataTools Object)
    => Proof
    -> Either UnificationError Proof
splitConstructor eq = 
    case getConclusion eq of 
    Equals_ _ _ a b -> 
        case (a, b) of 
        (App_ ha ca, App_ hb cb)
         | ha == hb  -> Right $ 
             useRule $ ModusPonens eq $ 
             instantiateForalls (reverse cb ++ reverse ca) $ 
             (assume $ generateInjectivityAxiom ha (getSort a) (map getSort ca))
         | otherwise -> Left $ ConstructorClash a b 
    otherwise -> impossible
    where instantiateForalls args pat = 
              foldr (\arg pat -> useRule $ ForallElim arg pat) pat args

generateInjectivityAxiom
    :: Given (MetadataTools Object)
    => SymbolOrAlias Object 
    -> Sort Object
    -> [Sort Object]
    -> Term
generateInjectivityAxiom head resultSort childrenSorts =
    let vars name = 
            zipWith 
                (\n sort -> varS (name ++ show n) sort)
                [1..]
                childrenSorts
        xVars = vars "x"
        xVars' = map Var_ xVars
        yVars = vars "y"
        yVars' = map Var_ yVars
        chainForall vars pat = foldl (\p v -> mkForall v p) pat (reverse vars) 
        fxEqfy = 
            mkApp head xVars'
            `mkEquals`
            mkApp head yVars'
        eqs = zipWith mkEquals xVars' yVars'
        conj = foldl1 mkAnd eqs
    in chainForall xVars $ chainForall yVars $ (fxEqfy `mkImplies` conj)

--testing:
--  putStrLn $ groom $ dummyEnvironment $ generateInjectivityAxiom (sym "f") (testSort "R") [testSort "A", testSort "B", testSort "C"]

flipEqn
    :: Given (MetadataTools Object)
    => Proof 
    -> Proof 
flipEqn eq = case getConclusion eq of 
    Equals_ _ _ a b -> 
      provableSubst eq [0] (useRule $ EqualityIntro a) 
      -- i.e. substitute a=b in the first position of a=a to get b=a

provableSubst 
    :: Given (MetadataTools Object)
    => Proof 
    -> Path 
    -> Proof 
    -> Proof
provableSubst eq path pat = case getConclusion eq of 
    Equals_ _ _ a b -> 
      useRule $ ModusPonens 
        pat
        (useRule $ ModusPonens 
            eq 
            (useRule $ EqualityElim 
                a 
                b 
                (getConclusion pat) 
                path
            )
        )
    _ -> impossible 

ex1 :: Given (MetadataTools Object) => [Proof]
ex1 =  [assume $ mkEquals (mkApp (sym "f") [Var_ $ var "a", mkApp (sym "g") [Var_ $ var "b", Var_ $ var "c"]]) (mkApp (sym "f") [Var_ $ var "d", Var_ $ var "e"]) ]

ex2 :: Given (MetadataTools Object) => [Proof]
ex2 =  [
  assume $ 
  mkEquals 
    (mkApp (sym "f") [Var_ $ var "a", mkApp (sym "g") [Var_ $ var "b", Var_ $ var "c"]])
    (mkApp (sym "f") [mkApp (sym "q") [Var_ $ var "d"], Var_ $ var "e"])
  ]


impossible = error "The impossible happened."
