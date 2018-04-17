{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.ASTTraversals ( koreBottomUpVisitor
                               , koreBottomUpVisitorM
                               , koreTopDownVisitor
                               , koreTopDownVisitorM
                               ) where


import           Control.Monad              ((>=>))
import           Data.Fix
import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.FixTraversals

{-|'koreTopDownVisitorM' is a generalized monadic visitor for patterns.
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
koreTopDownVisitorM
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
koreTopDownVisitorM preprocess postprocess =
    fixTopDownVisitorM
        fixPreprocess
        (unifiedPatternApply postprocess)
  where
    fixPreprocess =
        unifiedPatternApply
            (preprocess
            >=>
            \case
                Left r       -> return (Left r)
                Right (p, t) -> return (Right (unifyPattern p, t))
            )

{-|'bottomUpVisitorM' is the specialization of 'topDownVisitorM' where the
preprocessor function always requests the recursive visitation of its children,
basically resulting in a bottom-up visitor given by the aggregation function.

The aggreagation function provided as argument is a local visitor/reducer
which assumes that all children patterns of a pattern have been visited and
transformed into results and aggregates these results into a new result.
-}
koreBottomUpVisitorM
    :: (Monad m, UnifiedPatternInterface pat, Traversable (pat variable))
    => (forall level . MetaOrObject level
        => Pattern level variable result -> m result)
    -> (Fix (pat variable) -> m result)
koreBottomUpVisitorM reduce = cataM (unifiedPatternApply reduce)

-- |'koreTopDownVisitor' is the non-monadic version of 'koreTopDownVisitorM'.
koreTopDownVisitor
    :: (UnifiedPatternInterface pat, Functor (pat variable))
    => (forall level . MetaOrObject level
        => Pattern level variable (Fix (pat variable))
        -> Either result (Pattern level variable (Fix (pat variable)))
       )
    -> (forall level . MetaOrObject level
        => Pattern level variable result -> result)
    -> (Fix (pat variable) -> result)
koreTopDownVisitor preprocess postprocess =
    fixTopDownVisitor fixPreprocess fixPostprocess
  where
    fixPostprocess = unifiedPatternApply postprocess
    fixPreprocess = unifiedPatternApply (fmap unifyPattern . preprocess)

-- |'bottomUpVisitor' is the non-monadic version of 'bottomUpVisitorM'.
koreBottomUpVisitor
    :: (UnifiedPatternInterface pat, Functor (pat variable))
    => (forall level . MetaOrObject level
        => Pattern level variable result -> result)
    -> (Fix (pat variable) -> result)
koreBottomUpVisitor reduce = cata (unifiedPatternApply reduce)
