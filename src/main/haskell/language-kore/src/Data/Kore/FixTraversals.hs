{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.FixTraversals ( fixBottomUpVisitor
                               , fixBottomUpVisitorM
                               , fixTopDownVisitor
                               , fixTopDownVisitorM
                               ) where


import           Control.Monad.Identity
import           Data.Fix

{-|'fixTopDownVisitorM' is a generalized monadic visitor.
It takes as arguments a preprocess function and a postprocess function and
produces a function transforming a 'Fix' object into a monadic value.

@preprocess@ takes as argument an unfixed object and works in two modes:
* Transform the input directly into a result and skip the visiting recursion
* Transform the input into a pattern which will be visited recursively. It also
  returns a monad action modifier that will be used when visiting the object's
  children (use 'id' if you don't need one).

The @postprocess@ function assumes that all children of the object have
been visited and transformed into results and aggregates these results into a
new result.
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
