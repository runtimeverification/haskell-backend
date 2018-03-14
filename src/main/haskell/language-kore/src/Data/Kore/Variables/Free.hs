{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Variables.Free ( TermWithVariablesClass(freeVariables)
                                ) where

import           Data.Fix
import           Data.Foldable           (fold)
import qualified Data.Set                as Set
import           Data.Typeable           (Typeable)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.ASTTraversals

{-| 'TermWithVariableClass' links a @term@ type with a @var@ type and
provides 'freeVariables' for extracting the set of free variables of a term
-}
class TermWithVariablesClass term var | term -> var where
    freeVariables :: term -> Set.Set var

instance
    ( Typeable var
    , Ord (var Object)
    , Ord (var Meta)
    ) => TermWithVariablesClass (Fix (UnifiedPattern var)) (Unified var)
  where
    freeVariables = bottomUpVisitor freeVarsVisitor

freeVarsVisitor
    :: (MetaOrObject level, Typeable var, Ord (var Object), Ord (var Meta))
    => Pattern level var (Set.Set (Unified var))
    -> Set.Set (Unified var)
freeVarsVisitor (VariablePattern v) = Set.singleton (asUnified v)
freeVarsVisitor (ExistsPattern e) =
    Set.delete (asUnified (existsVariable e)) (existsChild e)
freeVarsVisitor (ForallPattern f) =
    Set.delete (asUnified (forallVariable f)) (forallChild f)
freeVarsVisitor p = fold p  -- default rule
