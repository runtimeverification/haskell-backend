{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Variables.Free ( TermWithVariablesClass(freeVariables)
                                ) where

import qualified Data.Set                as Set

import           Data.Kore.AST
import           Data.Kore.ASTTraversals

{-| 'TermWithVariableClass' links a @term@ type with a @var@ type and
provides 'freeVariables' for extracting the set of free variables of a term
-}
class TermWithVariablesClass term var where
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
    Set.delete (existsVariable e) (existsPattern e)
freeVarsVisitor (ForallPattern f) =
    Set.delete (forallVariable f) (forallPattern f)
freeVarsVisitor p = foldMap id p --default rule
