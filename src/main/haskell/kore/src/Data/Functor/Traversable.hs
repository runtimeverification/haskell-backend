module Data.Functor.Traversable where

import Control.Monad.Identity
import Data.Functor.Foldable

{-| Monadic catamorphism (generalized fold).

  @cataM@ is the monadic counterpart of 'cata' or 'fold'.

-}
cataM :: (Monad m, Traversable (Base t), Recursive t)
      => (Base t a -> m a) -> t -> m a
cataM f = cataM_go
  where
    cataM_go = (f =<<) . traverse cataM_go . project

{-| Monadic anamorphism (generalized unfold).

  @anaM@ is the monadic counterpart of 'ana' or 'unfold'.

-}
anaM :: (Monad m, Traversable (Base t), Corecursive t)
     => (a -> m (Base t a)) -> a -> m t
anaM f = anaM_go
  where
    anaM_go = fmap embed . (traverse anaM_go =<<) . f

{-| Monadic hylomorphism (generalized refold).

  @hyloM@ is the monadic counterpart of 'hylo' or 'refold'.

-}
hyloM :: (Monad m, Traversable f) => (f b -> m b) -> (a -> m (f a)) -> a -> m b
hyloM f g = h
  where
    h = (f =<<) . (traverse h =<<) . g

{-| 'fixTopDownVisitorM' is a generalized monadic visitor.
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
    :: (Monad m, Traversable (Base t), Recursive t)
    => (Base t t
        -> m (Either result (Base t t, m result -> m result))
       )
    -> (Base t result -> m result)
    -> (t -> m result)
fixTopDownVisitorM preprocess postprocess = self
  where
    self =
        preprocess . project
        >=> (\case
            Left r   -> return r
            Right (p', f) ->
                traverse (f . self) p' >>= postprocess
        )

{-| 'fixBottomUpVisitorM' is the specialization of 'fixTopDownVisitorM' where the
  preprocessor function always requests the recursive visitation of its children,
  basically resulting in a bottom-up visitor given by the aggregation function.

  The aggreagation function provided as argument is a local visitor/reducer
  which assumes that all children have been visited and
  transformed into results and aggregates these results into a new result.

-}
fixBottomUpVisitorM
    :: (Monad m, Traversable (Base t), Recursive t)
    => (Base t result -> m result) -> (t -> m result)
fixBottomUpVisitorM = cataM

-- | 'fixTopDownVisitor' is the non-monadic version of 'fixTopDownVisitorM'.
fixTopDownVisitor
    :: Recursive t
    => (Base t t -> Either result (Base t t))
    -> (Base t result -> result)
    -> (t -> result)
fixTopDownVisitor preprocess postprocess = self
  where
    self =
        (\case
            Left r   -> r
            Right p' -> postprocess (fmap self p')
        )
        . preprocess . project

{-| 'fixBottomUpVisitor' is the non-monadic version of 'fixBottomUpVisitorM'.

  See also: @cata@

-}
fixBottomUpVisitor
    :: Recursive t
    => (Base t result -> result)
    -> (t -> result)
fixBottomUpVisitor = cata
