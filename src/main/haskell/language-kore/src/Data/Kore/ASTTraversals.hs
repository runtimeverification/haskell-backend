{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE Rank2Types            #-}
module Data.Kore.ASTTraversals ( bottomUpVisitor
                               , bottomUpVisitorM
                               , topDownVisitor
                               , topDownVisitorM
                               ) where


import           Control.Monad.Identity
import           Data.Fix
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject

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
    :: (Monad m, Traversable pat)
    => (pat (Fix pat)
        -> m (Either result ( pat (Fix pat) , m result -> m result))
       )
    -> (pat result -> m result)
    -> (Fix pat -> m result)
topDownVisitorM preprocess postprocess = self
  where
    self = preprocess . unFix >=> (\p ->
        case p of
            Left r   -> return r
            Right (p', f) ->
                traverse (f . self) p' >>= postprocess
        )

{-|'bottomUpVisitorM' is the specialization of 'topDownVisitorM' where the
preprocessor function always requests the recursive visitation of its children,
basically resulting in a bottom-up visitor given by the aggregation function.

The aggreagation function provided as argument is a local visitor/reducer
which assumes that all children patterns of a pattern have been visited and
transformed into results and aggregates these results into a new result.
-}
bottomUpVisitorM
    :: (Monad m, Traversable pat)
    => (pat result -> m result) -> (Fix pat -> m result)
bottomUpVisitorM = cataM

-- |'topDownVisitor' is the non-monadic version of 'topDownVisitorM'.
topDownVisitor
    :: Functor pat
    => (pat (Fix pat) -> Either result (pat (Fix pat)))
    -> (pat result -> result)
    -> (Fix pat -> result)
topDownVisitor preprocess postprocess = self
  where
    self =
        (\p -> case p of
            Left r   -> r
            Right p' -> postprocess (fmap self p')
        )
        . preprocess . unFix


-- |'bottomUpVisitor' is the non-monadic version of 'bottomUpVisitorM'.
bottomUpVisitor
    :: Functor pat
    => (pat result -> result)
    -> (Fix pat -> result)
bottomUpVisitor = cata
