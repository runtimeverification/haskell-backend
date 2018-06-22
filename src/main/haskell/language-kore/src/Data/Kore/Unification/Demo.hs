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
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE ViewPatterns           #-}


module Data.Kore.Unification.Demo where

import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix
import           Data.List 

import           Control.Lens
import           Control.Lens.Operators
import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Monad.Except

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.PureML
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.IndexedModule.MetadataTools

import           Data.Kore.Unification.ProofSystemWithHypos
import           Data.Kore.Unification.UnificationRules
import           Data.Kore.Unification.UnificationAlgorithm
import           Data.Kore.Unparser.Unparse

import           Data.Kore.Unparser.Unparse

import Debug.Trace
import Text.Groom
spy x = trace (groom x) x

var x = 
  Fix $ VariablePattern $ Variable (noLocationId x) placeholderSort 

app x ys = Fix $ ApplicationPattern $ Application 
  { applicationSymbolOrAlias = x
  , applicationChildren = ys
  }

sym x = SymbolOrAlias 
  { symbolOrAliasConstructor = noLocationId x 
  , symbolOrAliasParams = [] 
  }

cabc :: Term 
cabc =
  app (sym "C") 
  [ var "a"
  , var "b"
  , var "c"
  ]

cadcaaa :: Term 
cadcaaa = 
  app (sym "C") 
  [ var "a"
  , app (sym "D") []
  , app (sym "C") 
    [ var "a"
    , var "a"
    , var "a"]
  ]

d :: Term
d = app (sym "D") []

eabcd :: Term 
eabcd = 
  app (sym "E")
  [ app (sym "E")
      [ var "a"
      , var "b"
      ]
  , app (sym "E")
      [ var "c"
      , var "d"
      ]
  ]

ebcda :: Term 
ebcda = 
  app (sym "E")
  [ app (sym "E")
      [ var "b"
      , var "c"
      ]
  , app (sym "E")
      [ var "d"
      , var "a"
      ]
  ]

exx :: Term 
exx = 
  app (sym "E")
  [ var "x"
  , var "x"
  ]

x :: Term
x = 
  var "x"

large2 :: Term
large1 = bigTerm 8 0

large1 :: Term 
large2 = bigTerm 8 1

bigTerm 0 k = var $ "v" ++ show k
bigTerm n k = app (sym "E") [ bigTerm (n-1) (k+1), bigTerm (n-1) (k*2)]

emptyProof :: Proof Int UnificationRules Term 
emptyProof = M.empty

emptyUnificationState = 
  UnificationState
  { _activeSet   = []
  , _finishedSet = []
  , _proof       = emptyProof
  }

dummyMetaTools = MetadataTools
    { isConstructor    = const True 
    , isFunctional     = const True 
    , getArgumentSorts = const [] 
    , getResultSort    = const placeholderSort
    }

-- putStrLn $ run example1
testUnify x y = putStrLn $ display $ runStack $ unificationProcedure x y
  
runStack = 
  runExcept .
  flip execStateT emptyUnificationState .
  flip runReaderT dummyMetaTools 

display :: Either UnificationError UnificationState -> String
display (Right state) = myShow (_proof state)
display (Left e) = show e

-- -- AWFUL HACK! I just wanted legible output as fast as possible
-- -- Pretty print properly soon.
-- display = 
--   unescapeLol . 
--   groomString .
--   -- (\(UnificationState activeSet finishedSet proof) -> 
--   --   (finishedSet, (fmap.fmap) UnparseWrapper proof)
--   -- ) . 
--   (\x -> case x of 
--     Right (UnificationState activeSet finishedSet proof) -> 
--       show (finishedSet, (fmap.fmap) (("\n" ++) . unparseToString) proof)
--     Left err -> show (err :: UnificationError)
--   ) 

-- unescapeLol [] = []
-- unescapeLol s = 
--   case (reads s, break (=='"') s) of 
--     ([(here, later)], _) -> here ++ unescapeLol later
--     (_, (earlier, here)) -> earlier ++ unescapeLol here  

class MyShow a where
  myShow :: a -> String

compactSpaces :: String -> String
compactSpaces [] = []
compactSpaces ('{':xs) = trimSortInfo xs
  where
    trimSortInfo ('}':xs) = compactSpaces xs
    trimSortInfo (_:xs) = trimSortInfo xs
    trimSortInfo [] = []
compactSpaces ('(':' ':xs) = compactSpaces ('(':xs)
compactSpaces (' ':')':xs) = compactSpaces (')':xs)
compactSpaces ('(':')':xs) = compactSpaces xs
compactSpaces (' ':' ':xs) = compactSpaces (' ':xs)
compactSpaces (':':'S':xs) = compactSpaces xs
compactSpaces (x:xs) = x : compactSpaces xs


compactIndentedOutput :: String -> String
compactIndentedOutput = concatMap $ \c ->
  case c of 
    '\t' -> ""
    '\n' -> " "
    c    -> [c]

instance Show a => MyShow (S.Set a) where
  myShow set = show $ S.toList set

instance MyShow Int where
  myShow = show

instance MyShow a => MyShow [a] where 
  myShow xs = "[" ++ intercalate "," (map myShow xs) ++ "]"

instance MyShow Term where 
  myShow (Equation _ _ a b) = myShow a ++ " = " ++ myShow b
  myShow (unFix -> VariablePattern (Variable v _)) = getId v
  myShow (unFix -> AndPattern (And _ a b)) = myShow a ++ " /\\ " ++ myShow b
  myShow (unFix -> ImpliesPattern (Implies _ a b)) = myShow a ++ " -> " ++ myShow b
  myShow (unFix -> IffPattern (Iff _ a b)) = myShow a ++ " <-> " ++ myShow b
  myShow (unFix -> ApplicationPattern (Application head children))
   = (getId $ symbolOrAliasConstructor head)
   ++ if null children then "" else "(" 
   ++ intercalate ", " (map myShow children) 
   ++ ")"

  -- myShow t = compactSpaces $ compactIndentedOutput $ unparseToString t

instance MyShow (Idx, ProofLine Idx UnificationRules Term) where 
  myShow (ix, line) = flip execState "" $ do 
   print $ myShow ix 
   print ":"
   align 5
   print $ myShow (claim line)
   align 80
   print "by "
   print $ myShow (justification line)
   align 160
   print "assuming "
   print $ myShow (assumptions line)
     where print s = do 
             text <- get 
             put (text ++ s)
           align m = do 
             text <- get 
             put (text ++ take (m - length text) (repeat ' '))

instance MyShow (Proof Idx UnificationRules Term) where 
  myShow m = unlines (map myShow $ M.toList m)

instance MyShow a => MyShow (UnificationRules a) where
  myShow Assumption = "assumption"
  myShow (Discharge x y) 
    = "discharging hypothesis " ++ myShow x ++ " from " ++ myShow y
  myShow (EqSymmetric x)
   = "symmetry of = on " ++ myShow x
  myShow (Refl x)
   = "reflexivity of = on " ++ myShow x
  myShow (LocalSubstitution x y p) 
   = "substituting " 
   ++ myShow x 
   ++ " in " 
   ++ myShow y 
   ++ " in position " 
   ++ myShow p
  myShow (NoConfusion x)
   = "no-confusion axiom on " ++ myShow x 
  myShow (AndIntro x y)
   = "conjunction of " ++ myShow x ++ " and " ++ myShow y
  myShow (AndL x)
   = "LHS of conjunction " ++ myShow x 
  myShow (AndR x)
   = "RHS of conjunction " ++ myShow x 
  myShow (ModusPonens x y )
   = "Modus ponens on " 
   ++ myShow x 
   ++ " and " 
   ++ myShow y
  myShow (IffIntro x y)
   = "if and only if on " 
   ++ myShow x 
   ++ " and " 
   ++ myShow y





