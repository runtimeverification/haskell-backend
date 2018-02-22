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
It takes as arguments a preprocess function and a postprocess function and
produces a function transforming a 'FixPattern' into a monadic value.

The preprocess function takes an unwrapped 'Pattern' and works in two modes:
* Transform the input directly into a result and skip the visiting recursion
* Transform the input into a pattern which will be visited recursively. It also
  returns a monad action modifier that will be used when visiting the pattern's
  children (use 'id' if you don't need one).

The postprocess function assumes that all children patterns of a pattern have
been visited and transformed into results and aggregates these results into a
new result.
-}
topDownVisitorM
    :: (FixPattern var fixedPoint, Monad m)
    => ( forall a . IsMeta a => Pattern a var (fixedPoint var)
        -> m
            ( Either
                result
                ( Pattern a var (fixedPoint var)
                , m result -> m result
                )
            )
        )
    -> (forall a . IsMeta a => Pattern a var result -> m result)
    -> (fixedPoint var -> m result)
topDownVisitorM preprocess postprocess = self
  where
    self = fixPatternApply (\p -> do
        preP <- preprocess p
        case preP of
            Left r   -> return r
            Right (p', f) -> do
                recP <- traverse (f . self) p'
                postprocess recP
        )

{-|'bottomUpVisitorM' is the specialization of 'topDownVisitorM' where the
preprocessor function always requests the recursive visitation of its children,
basically resulting in a bottom-up visitor given by the aggregation function.

The aggreagation function provided as argument is a local visitor/reducer
which assumes that all children patterns of a pattern have been visited and
transformed into results and aggregates these results into a new result.
-}
bottomUpVisitorM
    :: (FixPattern var fixedPoint, Monad m)
    => (forall a . IsMeta a => Pattern a var result -> m result)
    -> (fixedPoint var -> m result)
bottomUpVisitorM = topDownVisitorM (\x -> pure (Right (x, id)))

-- |'topDownVisitor' is the non-monadic version of 'topDownVisitorM'.
topDownVisitor
    :: FixPattern var fixedPoint
    => (forall a . IsMeta a => Pattern a var (fixedPoint var)
        -> Either result (Pattern a var (fixedPoint var)))
    -> (forall a . IsMeta a => Pattern a var result -> result)
    -> (fixedPoint var -> result)
topDownVisitor preprocess postprocess =
    runIdentity .
        topDownVisitorM preprocessM (pure . postprocess)
  where
    preprocessM x =
        case preprocess x of
            Left r  -> return (Left r)
            Right p -> return (Right (p, id))

-- |'bottomUpVisitor' is the non-monadic version of 'bottomUpVisitorM'.
bottomUpVisitor
    :: FixPattern var fixedPoint
    => (forall a . IsMeta a => Pattern a var result -> result)
    -> (fixedPoint var -> result)
bottomUpVisitor reduce =
    runIdentity . bottomUpVisitorM (pure . reduce)
