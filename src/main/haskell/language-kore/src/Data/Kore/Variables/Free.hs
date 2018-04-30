{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-|
Module      : Data.Kore.Variables.Free
Description : Specifies the 'TermWithVariablesClass' which is meant to define
              a term with variables and exports 'freeVariables'
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

-}
module Data.Kore.Variables.Free ( freeVariables
                                ) where

import           Data.Fix                   (Fix)
import           Data.Foldable              (fold)
import qualified Data.Set                   as Set

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTTraversals

{-| 'TermWithVariableClass' links a @term@ type with a @var@ type and
provides 'freeVariables' for extracting the set of free variables of a term
-}
freeVariables
    :: ( UnifiedPatternInterface pat
       , Functor (pat var)
       , Ord (var Object)
       , Ord (var Meta))
    => Fix (pat var) -> Set.Set (Unified var)
freeVariables = patternBottomUpVisitor freeVarsVisitor
    where
    freeVarsVisitor (VariablePattern v) = Set.singleton (asUnified v)
    freeVarsVisitor (ExistsPattern e) =
        Set.delete (asUnified (existsVariable e)) (existsChild e)
    freeVarsVisitor (ForallPattern f) =
        Set.delete (asUnified (forallVariable f)) (forallChild f)
    freeVarsVisitor p = fold p  -- default rule
