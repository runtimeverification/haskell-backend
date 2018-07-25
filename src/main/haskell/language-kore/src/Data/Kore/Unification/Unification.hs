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

{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
{-# OPTIONS_GHC -Wno-unused-matches    #-}
{-# OPTIONS_GHC -Wno-name-shadowing    #-}

module Data.Kore.Unification.Unification
( unificationProof
, exampleTerm1
, exampleTerm2 --only exported for now to make --pedantic shut up
) where



import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTUtils.SmartConstructors
import           Data.Kore.ASTUtils.Substitution
import           Data.Kore.IndexedModule.MetadataTools

import           Data.Kore.Proof.ConstructorAxioms
import           Data.Kore.Proof.Dummy
import           Data.Kore.Proof.Proof
import           Data.Kore.Proof.Util

import           Data.Hashable
import           Data.Reflection
import qualified Data.Set                              as S
import           GHC.Generics                          (Generic)

-- | Given terms `t1` and `t2`, outputs a proof that
-- `t1 /\ t2 <-> t1 /\ <MGU EQNS>`, where `<MGU EQNS>` is
-- a conjunction of the most general unifier equations.
unificationProof
    :: Given (MetadataTools Object)
    => Term
    -> Term
    -> Either UnificationError Proof
unificationProof a b = do
    forwards <- unificationForwardsProof a b
    let mguEqns =
            case getConclusion forwards of
                     Implies_ _ _ b -> b
                     _              -> impossible
    let backwards = unificationBackwardsProof mguEqns a b
    return $ useRule $ AndIntro forwards backwards

unificationBackwardsProof
    :: Given (MetadataTools Object)
    => Term -- conjunction of eqs
    -> Term -- LHS
    -> Term -- RHS
    -> Proof
unificationBackwardsProof eqns a b = useRule $ Discharge eqns aEqb
    where eqns' = andElimN $ assume eqns
          transform k p =
            foldr
            (\eq p -> provablySubstitute eq [k] p)
            (useRule $ EqualityIntro p) eqns'
          aEqSubstA = transform 1 a
          substBEqB = transform 0 b
          aEqb = provablySubstitute substBEqB [1] aEqSubstA

unificationForwardsProof
    :: Given (MetadataTools Object)
    => Term
    -> Term
    -> Either UnificationError Proof
unificationForwardsProof a b = do
    proof <- go [] [assume $ mkEquals a b]
    return $ useRule $ Discharge (mkEquals a b) proof
        where
          go finished [] = return $ andIntroN finished
          go finished (eq : eqs) = case getConclusion eq of
              And_ s a b -> go finished $
                useRule (AndElimL eq) : useRule (AndElimR eq) : eqs
              Equals_ s1 s2 (Var_ x) b
                | occursCheck eq ->
                    go (eq : finished) (map (provablySubstitute eq []) eqs)
                | otherwise ->
                    Left $ OccursCheck eq
              Equals_ s1 s2 a (Var_ x) -> go finished (flipEqn eq : eqs)
              Equals_ s1 s2 a b -> do
                eq' <- splitConstructor eq
                go finished (eq' : eqs)
              _ -> impossible

data UnificationError
  = ConstructorClash Term Term
  | OccursCheck Proof
  deriving(Show, Generic)

instance Hashable UnificationError


-- | Returns False if the eq x = t fails the occurs check,
-- i.e. returns False iff x appears in t.
occursCheck
    :: Given (MetadataTools Object)
    => Proof
    -> Bool
occursCheck eq = case getConclusion eq of
    Equals_ _ _ (Var_ v) rhs -> not $ S.member v (freeVars rhs)
    _                        -> impossible

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
             forallElimN (ca ++ cb) $
             (assume $ generateInjectivityAxiom ha (getSort a) (map getSort ca))
         | otherwise -> Left $ ConstructorClash a b
        _ -> impossible
    otherwise -> impossible

flipEqn
    :: Given (MetadataTools Object)
    => Proof
    -> Proof
flipEqn eq = case getConclusion eq of
    Equals_ _ _ a b ->
      provablySubstitute eq [0] (useRule $ EqualityIntro a)
      -- i.e. substitute a=b in the first position of a=a to get b=a
    _ -> impossible


--testing:
--  putStrLn $ groom $ dummyEnvironment $ generateInjectivityAxiom (sym "f") (testSort "R") [testSort "A", testSort "B", testSort "C"]

-- f(a,g(b,c)) = f(d,e)
exampleTerm1 :: Given (MetadataTools Object) => Term
exampleTerm1 =
    (mkApp (sym "f")
        [Var_ $ var "a", mkApp (sym "g")
        [Var_ $ var "b", Var_ $ var "c"]]
    )

exampleTerm2 :: Given (MetadataTools Object) => Term
exampleTerm2 =
    (mkApp (sym "f") [Var_ $ var "d", Var_ $ var "e"])



