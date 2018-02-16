{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.ASTTraversals ( bottomUpVisitor
                               , bottomUpVisitorM
                               , topDownVisitor
                               , topDownVisitorM
                               ) where


import           Control.Monad.Identity
import           Data.Kore.AST

{-|'topDownVisitorM' is a generalized monadic visitor for patterns.
It takes as arguments a preprocess function and a postprocess function and produces a function transforming a 'FixPattern' into a monadic value.

The preprocess function takes an unwrapped Pattern and can either skip
the visiting recursion and transform it directly into a result, or it can
transform it as a pattern but still leave it to be recursively visited.

The postprocess function assumes that all children patterns of a pattern have
been visited and transformed into results and aggregates these results to a
new result.
-}
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

{-|'bottomUpVisitorM' is the specialization of 'topDownVisitorM' where the
preprocessor function always requests the recursive visitation of its children,
basically resulting in a bottom-up visitor given by the aggregation function.

It takes as argument a local visitor/reduce function which reduces to a result
parameterized patterns containing in any pattern position the result of
visiting that pattern.
-}
bottomUpVisitorM
    :: (FixPattern var fixedPoint, Monad m)
    => (forall a . IsMeta a => Pattern a var result -> m result)
    -> (fixedPoint var -> m result)
bottomUpVisitorM = topDownVisitorM (pure . Right)

-- |'topDownVisitor' is the non-monadic version of 'topDownVisitorM'.
topDownVisitor
    :: FixPattern var fixedPoint
    => (forall a . IsMeta a => Pattern a var (fixedPoint var)
        -> Either result (Pattern a var (fixedPoint var)))
    -> (forall a . IsMeta a => Pattern a var result -> result)
    -> (fixedPoint var -> result)
topDownVisitor preprocess postprocess =
    runIdentity . topDownVisitorM (pure . preprocess) (pure . postprocess)

-- |'bottomUpVisitor' is the non-monadic version of 'bottomUpVisitorM'.
bottomUpVisitor
    :: FixPattern var fixedPoint
    => (forall a . IsMeta a => Pattern a var result -> result)
    -> (fixedPoint var -> result)
bottomUpVisitor reduce =
    runIdentity . bottomUpVisitorM (pure . reduce)
