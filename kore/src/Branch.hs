{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE UndecidableInstances #-}

module Branch
    ( BranchT (..)
    , mapBranchT
    , gather
    , gatherAll
    , scatter
    , foldBranchT
    , alternate
    ) where

import Control.Applicative
import qualified Control.Monad as Monad
import Control.Monad.Reader
import Control.Monad.State.Class
    ( MonadState
    )
import qualified Data.Foldable as Foldable
import Data.Typeable

import Kore.Logger
import Kore.Profiler.Data
    ( MonadProfiler (..)
    )
import ListT
    ( ListT (..)
    , mapListT
    )
import qualified ListT
import SMT
    ( MonadSMT (..)
    )

{- | 'BranchT' extends any 'Monad' with disjoint branches.

Broadly, one goal of simplification is to promote 'Or' (disjunction) to the top
level. Many @Simplifier@s return a 'MultiOr' for this reason; we can think of
this as external branching. @BranchT Simplifier@ also allows branching through
'Alternative'. Branches are created with '<|>':
@
let
    simplifier1 :: BranchT Simplifier a
    simplifier2 :: BranchT Simplifier a
in
    simplifier1 <|> simplifier2  -- A 'BranchT Simplifier' with two branches.
@

Branches are pruned with 'empty':
@
simplify :: BranchT Simplifier a
simplify = do
    unless condition empty
    continue  -- This simplifier would not be reached if "condition" is 'False'.
@

Use 'scatter' and 'gather' to translate between the two forms of branches.

-}
-- TODO (thomas.tuegel): Replace Alternative with an interface that doesn't
-- assume associativity, then replace ListT with a free monad.
-- TODO (thomas.tuegel): Do not export constructors of BranchT.
newtype BranchT m a =
    -- Pay no attention to the ListT behind the curtain!
    BranchT (ListT.ListT m a)
    deriving (Functor, Applicative, Monad)
    deriving (Alternative, MonadPlus, Foldable)
    deriving MonadTrans
    deriving MonadIO
    deriving Typeable

deriving instance MonadReader r m => MonadReader r (BranchT m)

deriving instance MonadState s m => MonadState s (BranchT m)

deriving instance WithLog msg m => WithLog msg (BranchT m)

deriving instance MonadSMT m => MonadSMT (BranchT m)

deriving instance MonadProfiler m => MonadProfiler (BranchT m)

mapBranchT :: Monad m => (forall x. m x -> m x) -> BranchT m a -> BranchT m a
mapBranchT f (BranchT listT) = BranchT (ListT.mapListT f listT)

{- | Collect results from many simplification branches into one result.

@gather@ returns all the results of a @'BranchT' m a@ in a single list.

Examples:

@
gather (pure a <|> pure b) === pure [a, b]
@

@
gather empty === pure []
@

See also: 'scatter'

 -}
gather :: Monad m => BranchT m a -> m [a]
gather (BranchT simpl) = ListT.gather simpl

{- | Collect results from many simplification branches into one result.

@gather@ returns all the results of a @'BranchT' m a@ in a single disjunction
('MultiOr'). @gather@ strips away the @BranchT@ transformer so that it always
returns one result.

See also: 'scatter', 'gather'

 -}
gatherAll :: Monad m => BranchT m [a] -> m [a]
gatherAll simpl = Monad.join <$> gather simpl

{- | Disperse results into many simplification branches.

Examples:

@
scatter [a, b] === (pure a <|> pure b)
@

@
scatter [] === empty
@

See also: 'gather'

 -}
scatter :: (Applicative m, Foldable f) => f a -> BranchT m a
scatter = BranchT . ListT.scatter . Foldable.toList

{- | Fold down a 'BranchT' into its base 'Monad'.

See also: 'foldListT'

 -}
foldBranchT :: Monad m => (a -> m r -> m r) -> m r -> BranchT m a -> m r
foldBranchT f mr (BranchT listT) = foldListT listT f mr

{- | Fold down a 'BranchT' using an underlying 'Alternative'.

See also: 'foldBranchT'

 -}
alternate :: (Alternative m, Monad m) => BranchT m a -> m a
alternate = foldBranchT ((<|>) . pure) empty
