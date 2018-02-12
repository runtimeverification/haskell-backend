{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.ASTTraversals ( bottomUpVisitor
                               , bottomUpVisitorM
                               , freeVariables
                               , topDownVisitor
                               , topDownVisitorM
                               ) where

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
    runIdentity . topDownVisitorM (return . Right) (pure . reduce)

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

freeVariables
    :: VariableClass var
    => FixedPattern var -> [UnifiedVariable var]
freeVariables = bottomUpVisitor freeVarsVisitor

freeVarsVisitor
    :: (Typeable var, IsMeta a, Show (var Object), Show (var Meta),
        Eq (UnifiedVariable var))
    => Pattern a var [UnifiedVariable var] -> [UnifiedVariable var]
freeVarsVisitor (VariablePattern v) = [asUnifiedVariable v]
freeVarsVisitor (ExistsPattern e) =
    filter (/= existsVariable e) (existsPattern e)
freeVarsVisitor (ForallPattern f) =
    filter (/= forallVariable f) (forallPattern f)
freeVarsVisitor p = foldMap id p --default rule
