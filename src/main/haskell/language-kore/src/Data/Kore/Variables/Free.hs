{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Variables.Free ( TermWithVariablesClass(freeVariables)
                                ) where

import qualified Data.Set                as Set
import           Data.Typeable           (Typeable)

import           Data.Kore.AST
import           Data.Kore.ASTTraversals

class TermWithVariablesClass term var where
    freeVariables :: term -> Set.Set var

instance VariableClass var
    => TermWithVariablesClass (FixedPattern var) (UnifiedVariable var) where
    freeVariables = bottomUpVisitor freeVarsVisitor

freeVarsVisitor
    :: (Typeable var, IsMeta a, Show (var Object), Show (var Meta),
        Eq (UnifiedVariable var), Ord (UnifiedVariable var))
    => Pattern a var (Set.Set (UnifiedVariable var))
    -> Set.Set (UnifiedVariable var)
freeVarsVisitor (VariablePattern v) = Set.singleton (asUnifiedVariable v)
freeVarsVisitor (ExistsPattern e) =
    Set.delete (existsVariable e) (existsPattern e)
freeVarsVisitor (ForallPattern f) =
    Set.delete (forallVariable f) (forallPattern f)
freeVarsVisitor p = foldMap id p --default rule
