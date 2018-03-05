{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Data.Kore.Variables.Free ( TermWithVariablesClass(freeVariables)
                                ) where

import           Data.Foldable           (fold)
import qualified Data.Set                as Set

import           Data.Kore.AST
import           Data.Kore.ASTTraversals

{-| 'TermWithVariableClass' links a @term@ type with a @var@ type and
provides 'freeVariables' for extracting the set of free variables of a term
-}
class TermWithVariablesClass term var | term -> var where
    freeVariables :: term -> Set.Set var

instance VariableClass var
    => TermWithVariablesClass (FixedPattern var) (UnifiedVariable var) where
    freeVariables = bottomUpVisitor freeVarsVisitor

freeVarsVisitor
    :: (IsMeta a, VariableClass var)
    => Pattern a var (Set.Set (UnifiedVariable var))
    -> Set.Set (UnifiedVariable var)
freeVarsVisitor (VariablePattern v) = Set.singleton (asUnified v)
freeVarsVisitor (ExistsPattern e) =
    Set.delete (asUnified (existsVariable e)) (existsChild e)
freeVarsVisitor (ForallPattern f) =
    Set.delete (asUnified (forallVariable f)) (forallChild f)
freeVarsVisitor p = fold p  -- default rule
