{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
{-|
Module      : Data.Kore.ASTTraversals
Description : Defines traversals functions for terms defined using 'Fix' points.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module is an extension of the 'Data.Fix' module, aimed toward supporting
visiting and transforming ASTs.  To this aim, the 'cata' and 'cataM' functions
provided by 'Data.Fix' were rebranded to 'fixBottomUpVisitor' and
'fixBottomUpVisitorM', as providing a "bottom-up" visiting pattern, two more
functions, 'fixTopDownVisitor' and 'fixTopDownVisitorM' were added to give more
control over the traversal process, and two specializations of the top-down
visitors to the case where a transformation rather than a visitation is needed
('fixTopDownTransformer' and 'fixTopDownTransformerM').

The functions in this module can be used directly to visit and transform
PurePattern objects.
-}
module Data.Kore.FixTraversals ( fixBottomUpVisitor
                               , fixBottomUpVisitorM
                               , fixTopDownVisitor
                               , fixTopDownVisitorM
                               , fixTopDownTransformer
                               , fixTopDownTransformerM
                               ) where


import           Control.Monad.Identity
import           Data.Fix

{-|'fixTopDownVisitorM' is a generalized monadic visitor.
It takes as arguments a preprocess function and a postprocess function and
produces a function transforming a 'Fix' object into a monadic value.

The @preprocess@ function takes as argument an unfixed object and works in two
modes:
* Left case:
    It transforms the input directly into a result and skips the visiting
    recursion
* Right case:
    It (sligthly) transforms the input into an object which will be further
    visited recursively.
    This case must also return a monad action modifier that will be used
    to update the results of visiting the object's children
    (use 'id' if you don't need one).

The @postprocess@ function assumes that all children of the object have
been visited and transformed into results and aggregates these results into a
new result.

Briefly, given a fixed object @p@ and functions @preprocess@ and @postprocess@,
`fixTopDownVisitorM' performs the following actions:

1. calls @preprocess@ on @p@ and,
2. if preprocess returns @Left result@, then it returns that
else, assume preprocess returns @Right (p', trans)@
3.1 applies 'patternTopDownVisitorM' on the direct children of @p'@
3.2 applies @trans@ on the results of (3.1)
3.3 applies @postprocess@ on the @p''@ obtained from @p'@ by replacing
    its direct children with the corresponding results from (3.2)
-}
fixTopDownVisitorM
    :: (Monad m, Traversable pat)
    => (pat (Fix pat)
        -> m (Either result ( pat (Fix pat) , m result -> m result))
       )
    -> (pat result -> m result)
    -> (Fix pat -> m result)
fixTopDownVisitorM preprocess postprocess = self
  where
    self =
        preprocess . unFix
        >=> (\case
            Left r   -> return r
            Right (p', f) ->
                traverse (f . self) p' >>= postprocess
        )

{-|'fixTopDownTransformerM; is the specialization of 'fixTopDownVisitorM' to the
case in which the purpose of the visitation is to transform the original fixed
object to another of the same type. To ease its usage, the local transformation
functions have as result unfixed patterns, thus matching the type of their
input.
-}
fixTopDownTransformerM
    :: (Monad m, Traversable pat)
    => (pat (Fix pat)
        -> m
            (Either
                (pat (Fix pat))
                ( pat (Fix pat) , m (pat (Fix pat)) -> m (pat (Fix pat)))
            )
       )
    -> (pat (Fix pat) -> m (pat (Fix pat)))
    -> (Fix pat -> m (Fix pat))
fixTopDownTransformerM preTransform postTransform =
    fixTopDownVisitorM preprocess postprocess
  where
    preprocess x = do
        pre <- preTransform x
        case pre of
            Left p        -> return (Left (Fix p))
            Right (p, mf) -> return (Right (p, fmap Fix . mf . fmap unFix))
    postprocess = fmap Fix . postTransform

-- |'fixTopDownTransformer' is the non-monadic version of
--  'fixTopDownTransformerM'
fixTopDownTransformer
    :: Functor pat
    => (pat (Fix pat) -> Either (pat (Fix pat)) (pat (Fix pat)))
    -> (pat (Fix pat) -> pat (Fix pat))
    -> (Fix pat -> Fix pat)
fixTopDownTransformer preTransform postTransform =
    fixTopDownVisitor preprocess postprocess
  where
    preprocess x =
        case preTransform x of
            Left p  -> Left (Fix p)
            Right p -> Right p
    postprocess = Fix . postTransform



{-|'fixBottomUpVisitorM' is the specialization of 'fixTopDownVisitorM' where the
preprocessor function always requests the recursive visitation of its children,
basically resulting in a bottom-up visitor given by the aggregation function.

The aggreagation function provided as argument is a local visitor/reducer
which assumes that all children have been visited and
transformed into results and aggregates these results into a new result.
-}
fixBottomUpVisitorM
    :: (Monad m, Traversable pat)
    => (pat result -> m result) -> (Fix pat -> m result)
fixBottomUpVisitorM = cataM

-- |'fixTopDownVisitor' is the non-monadic version of 'fixTopDownVisitorM'.
fixTopDownVisitor
    :: Functor pat
    => (pat (Fix pat) -> Either result (pat (Fix pat)))
    -> (pat result -> result)
    -> (Fix pat -> result)
fixTopDownVisitor preprocess postprocess = self
  where
    self =
        (\case
            Left r   -> r
            Right p' -> postprocess (fmap self p')
        )
        . preprocess . unFix

-- |'fixBottomUpVisitor' is the non-monadic version of 'fixBottomUpVisitorM'.
fixBottomUpVisitor
    :: Functor pat
    => (pat result -> result)
    -> (Fix pat -> result)
fixBottomUpVisitor = cata
