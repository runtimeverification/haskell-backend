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
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}

module Data.Kore.Unification.Demo where

import qualified Data.Set as S
import qualified Data.Map as M
import           Data.Fix
import           Data.List 

import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Monad.Except

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.IndexedModule.MetadataTools

import           Data.Kore.Proof.ProofSystemWithHypos
import           Data.Kore.Unification.UnificationRules
import           Data.Kore.Unification.UnificationAlgorithm

var :: MetaOrObject level => String -> Term level
var x = 
  Fix $ VariablePattern $ Variable (noLocationId x) placeholderSort 

app :: MetaOrObject level => String -> [Term level] -> Term level
app x ys = Fix $ ApplicationPattern $ Application 
  { applicationSymbolOrAlias = sym x
  , applicationChildren = ys
  }
  where sym x = 
          SymbolOrAlias 
            { symbolOrAliasConstructor = noLocationId x 
            , symbolOrAliasParams = [] 
            }

pab :: MetaOrObject level => Term level  
pab =
  app "Pair"
  [ app "A" []
  , app "B" []
  ]

pxy :: MetaOrObject level => Term level  
pxy =
  app "Pair"
  [ var "x"
  , var "y"
  ]

cabc :: MetaOrObject level => Term level  
cabc =
  app "C"
  [ var "a"
  , var "b"
  , var "c"
  ]

cadcaaa :: MetaOrObject level => Term level  
cadcaaa = 
  app "C"
  [ var "a"
  , app "D" []
  , app "C"
    [ var "a"
    , var "a"
    , var "a"]
  ]

d :: MetaOrObject level => Term level 
d = app "D" []

eabcd :: MetaOrObject level => Term level  
eabcd = 
  app "E"
  [ app "E"
      [ var "a"
      , var "b"
      ]
  , app "E"
      [ var "c"
      , var "d"
      ]
  ]

ebcda :: MetaOrObject level => Term level  
ebcda = 
  app "E"
  [ app "E"
      [ var "b"
      , var "c"
      ]
  , app "E"
      [ var "d"
      , var "a"
      ]
  ]

exx :: MetaOrObject level => Term level 
exx = 
  app "E"
  [ var "x"
  , var "x"
  ]

large2 :: MetaOrObject level => Term level 
large1 = bigTerm 8 0

large1 :: MetaOrObject level => Term level 
large2 = bigTerm 8 1

bigTerm 
  :: MetaOrObject level 
  => Int 
  -> Int 
  -> Term level 
bigTerm 0 k = var $ "v" ++ show k
bigTerm n k = app "E" [ bigTerm (n-1) (k+1), bigTerm (n-1) (k*2)]

emptyProof :: Proof Int (UnificationRules level) (Term level) 
emptyProof = M.empty

emptyUnificationState
  :: MetaOrObject level 
  => UnificationState level 
emptyUnificationState = 
  UnificationState
  { _activeSet   = []
  , _finishedSet = []
  , _proof       = emptyProof
  }

dummyMetaTools 
  :: MetaOrObject level 
  => MetadataTools level
dummyMetaTools = MetadataTools
    { isConstructor    = const True 
    , isFunctional     = const True 
    , getArgumentSorts = const [] 
    , getResultSort    = const placeholderSort
    }

testUnify
  :: MetaOrObject level 
  => Term level 
  -> Term level
  -> IO ()
testUnify x y = putStrLn $ display $ runStack $ unificationProcedure x y
  
runStack
  :: MetaOrObject level
  => Unification level Idx 
  -> Either (UnificationError level) (UnificationState level)
runStack = 
  runExcept .
  flip execStateT emptyUnificationState .
  flip runReaderT dummyMetaTools 

display 
  :: MetaOrObject level
  => Either (UnificationError level) (UnificationState level) 
  -> String
display (Right state) = myShow (_proof state)
display (Left e) = show e

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

instance MetaOrObject level => MyShow (Term level) where 
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
  myShow _ = error "Add constructors here"

  -- myShow t = compactSpaces $ compactIndentedOutput $ unparseToString t

instance MetaOrObject level 
  => MyShow (Idx, ProofLine Idx (UnificationRules level) (Term level)) where 
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

instance MetaOrObject level 
  => MyShow (Proof Idx (UnificationRules level) (Term level)) where 
  myShow m = unlines (map myShow $ M.toList m)

instance (MetaOrObject level, MyShow a) 
  => MyShow (UnificationRules level a) where
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
  myShow _ = error "Add constructors here"





