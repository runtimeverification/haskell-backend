{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.ASTTraversals ( bottomUpVisitor
                               , bottomUpVisitorM
                               , freeVariables
                               , topDownVisitor
                               , topDownVisitorM
                               , TermWithVariablesClass
                               ) where

import qualified Data.Set               as Set
import           Data.Typeable          (Typeable)

import           Control.Monad.Identity
import           Data.Kore.AST

{-|'bottomUpVisitor' is the specialization of a catamorphism for patterns.
It takes as argument a local visitor/reduce function which reduces to a result
parameterized patterns containing in any pattern position the result of
visiting that pattern.
-}
bottomUpVisitorM
    :: (FixPattern var fixedPoint, Monad m)
    => (forall a . IsMeta a => Pattern a var result -> m result)
    -> (fixedPoint var -> m result)
bottomUpVisitorM = topDownVisitorM (pure . Right)

bottomUpVisitor
    :: FixPattern var fixedPoint
    => (forall a . IsMeta a => Pattern a var result -> result)
    -> (fixedPoint var -> result)
bottomUpVisitor reduce =
    runIdentity . bottomUpVisitorM (pure . reduce)

topDownVisitorM
    :: (FixPattern var fixedPoint, Monad m)
    => (forall a . IsMeta a => Pattern a var (fixedPoint var)
        -> m (Either result (Pattern a var (fixedPoint var))))
    -> (forall a . IsMeta a => Pattern a var result -> m result)
    -> (fixedPoint var -> m result)
topDownVisitorM preprocess postprocess = self
  where
    self = unFixPattern (\p -> do
        preP <- preprocess p
        case preP of
            Left r   -> return r
            Right p' -> do
                recP <- sequence (fmap self p')
                postprocess recP
        )

topDownVisitor
    :: FixPattern var fixedPoint
    => (forall a . IsMeta a => Pattern a var (fixedPoint var)
        -> Either result (Pattern a var (fixedPoint var)))
    -> (forall a . IsMeta a => Pattern a var result -> result)
    -> (fixedPoint var -> result)
topDownVisitor preprocess postprocess =
    runIdentity . topDownVisitorM (pure . preprocess) (pure . postprocess)

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
