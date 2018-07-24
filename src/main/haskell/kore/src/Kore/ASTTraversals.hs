{-|
Module      : Kore.ASTTraversals
Description : Defines traversals functions for patterns of
              `UnifiedPatternInterface` class.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable

This module provides a specialization of the functionality described in
the 'Data.Functor.Traversable' module to the case of Kore patterns.

This specialization is meant to allow the user to write the local
@preprocess@ and @postprocess@ functions to be written directly at the 'Pattern'
level, although the visitation process takes place on 'KorePattern's, which
requires several layers of constructors (including 'Fix') over Pattern.
-}
module Kore.ASTTraversals
    ( patternBottomUpVisitor
    , patternBottomUpVisitorM
    , patternTopDownVisitor
    , patternTopDownVisitorM
    ) where


import Control.Monad
       ( (>=>) )
import Data.Functor.Foldable

import Data.Functor.Traversable
import Kore.AST.Common
import Kore.AST.MetaOrObject

{-|'patternTopDownVisitorM' is a generalized monadic visitor for Kore patterns.
It takes as arguments a preprocess function and a postprocess function and
produces a function transforming a 'KorePattern' into a monadic value.

The preprocess function takes an unwrapped 'Pattern' and works in two modes:
* Left case:
    It transforms the input directly into a result and skips the visiting
    recursion
* Right case:
    It transforms the input into a pattern which will be visited recursively.
    This case must also return a monad action modifier that will be used
    to update the results of visiting the pattern's children
    (use 'id' if you don't need one).

The postprocess function assumes that all children patterns of a pattern have
been visited and transformed into results and aggregates these results into a
new result.

Briefly, given a pattern @p@ and functions @preprocess@ and @postprocess@,
`patternTopDownVisitorM' performs the following actions:

1. calls @preprocess@ on @p@ and,
2. if preprocess returns @Left result@, then it returns that
else, assume preprocess returns @Right (p', trans)@
3.1 applies 'patternTopDownVisitorM' on the direct children of @p'@
3.2 applies @trans@ on the results of (3.1)
3.3 applies @postprocess@ on the @p''@ obtained from @p'@ by replacing
    its direct children with the corresponding results from (3.2)
-}
patternTopDownVisitorM
    :: (Monad m, UnifiedPatternInterface pat, Traversable (pat variable))
    => (forall level . (MetaOrObject level)
        => Pattern level variable (Fix (pat variable))
        -> m (Either result ( Pattern level variable (Fix (pat variable))
                            , m result -> m result
                            )
             )
       )
    -> (forall level . MetaOrObject level
        => Pattern level variable result -> m result
       )
    -> (Fix (pat variable) -> m result)
patternTopDownVisitorM preprocess postprocess =
    fixTopDownVisitorM
        fixPreprocess
        (unifiedPatternApply postprocess)
  where
    {-
    fixPreprocess
        :: (pat' (Fix pat')
        -> m (Either result ( pat' (Fix pat') , m result -> m result))
        )
      where pat' = pat variable
    -}
    fixPreprocess =
        unifiedPatternApply
            (preprocess
            >=>
            \case
                Left r       -> return (Left r)
                Right (p, t) -> return (Right (unifyPattern p, t))
            )

{-|'patternBottomUpVisitorM' is the specialization of 'patternTopDownVisitorM' where
the preprocessor function always requests the recursive visitation of its
children, basically resulting in a bottom-up visitor given by the aggregation
function.

The aggreagation function provided as argument is a local visitor/reducer
which assumes that all children patterns of a pattern have been visited and
transformed into results and aggregates these results into a new result.
-}
patternBottomUpVisitorM
    :: (Monad m, UnifiedPatternInterface pat, Traversable (pat variable))
    => (forall level . MetaOrObject level
        => Pattern level variable result -> m result)
    -> (Fix (pat variable) -> m result)
patternBottomUpVisitorM reduce =
    fixBottomUpVisitorM (unifiedPatternApply reduce)

-- |'patternTopDownVisitor' is the non-monadic version of 'patternTopDownVisitorM'.
patternTopDownVisitor
    :: (UnifiedPatternInterface pat, Functor (pat variable))
    => (forall level . MetaOrObject level
        => Pattern level variable (Fix (pat variable))
        -> Either result (Pattern level variable (Fix (pat variable)))
       )
    -> (forall level . MetaOrObject level
        => Pattern level variable result -> result)
    -> (Fix (pat variable) -> result)
patternTopDownVisitor preprocess postprocess =
    fixTopDownVisitor fixPreprocess fixPostprocess
  where
    fixPostprocess = unifiedPatternApply postprocess
    fixPreprocess = unifiedPatternApply (fmap unifyPattern . preprocess)

-- |'patternBottomUpVisitor' is the non-monadic version of 'patternBottomUpVisitorM'.
patternBottomUpVisitor
    :: (UnifiedPatternInterface pat, Functor (pat variable))
    => (forall level . MetaOrObject level
        => Pattern level variable result -> result)
    -> (Fix (pat variable) -> result)
patternBottomUpVisitor reduce = fixBottomUpVisitor (unifiedPatternApply reduce)
