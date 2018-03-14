{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.ASTTraversals {-( bottomUpVisitor
                               , bottomUpVisitorM
                               , topDownVisitor
                               , topDownVisitorM
                               )-} where


import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore

import           Control.Monad.Identity
import           Data.Fix

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
    :: Monad m
    => ( forall level . MetaOrObject level
        => Pattern level var (FixedUnifiedPattern var)
            -> m
                ( Either
                    result
                    ( Pattern level var (FixedUnifiedPattern var)
                    , m result -> m result
                    )
                )
            )
    -> (forall level . MetaOrObject level
        => Pattern level var result -> m result)
    -> (FixedUnifiedPattern var -> m result)
topDownVisitorM preprocess postprocess = self
  where
    self = applyKorePattern (\p -> do
        preP <- preprocess p
        case preP of
            Left r   -> return r
            Right (p', f) -> do
                recP <- traverse (f . self) p'
                postprocess recP)

{-|'bottomUpVisitorM' is the specialization of 'topDownVisitorM' where the
preprocessor function always requests the recursive visitation of its children,
basically resulting in a bottom-up visitor given by the aggregation function.

The aggreagation function provided as argument is a local visitor/reducer
which assumes that all children patterns of a pattern have been visited and
transformed into results and aggregates these results into a new result.
-}
bottomUpVisitorM
    :: Monad m
    => (forall level . MetaOrObject level
        => Pattern level var result -> m result)
    -> (FixedUnifiedPattern var -> m result)
bottomUpVisitorM f = cataM (applyUnifiedPattern f)

-- |'topDownVisitor' is the non-monadic version of 'topDownVisitorM'.
topDownVisitor
    :: (forall level . MetaOrObject level
        => Pattern level var (FixedUnifiedPattern var)
            -> Either result (Pattern level var (FixedUnifiedPattern var)))
    -> (forall level . MetaOrObject level
        => Pattern level var result -> result)
    -> (FixedUnifiedPattern var -> result)
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
    :: (forall level . MetaOrObject level => Pattern level var result -> result)
    -> (FixedUnifiedPattern var -> result)
bottomUpVisitor f = cata (applyUnifiedPattern f)
