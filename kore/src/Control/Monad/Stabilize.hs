{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Control.Monad.Stabilize
    ( StabilizeT
    , stabilize
    , unstable
    , stable
    ) where

import           Control.Error
                 ( MaybeT )
import qualified Control.Error as Error
import qualified Control.Monad as Monad
import           Control.Monad.Morph
                 ( MFunctor, MonadTrans )
import qualified Control.Monad.Morph as Monad
import           Control.Monad.State.Strict
                 ( StateT, evalStateT )
import qualified Control.Monad.State.Strict as Monad.State
import           Data.Function
                 ( (&) )

{- | The stabilizable monad transformer.

The computation terminates upon the second consecutive call to 'stable',
i.e. two 'stable' steps with no intermediate 'unstable' steps.

See also: 'stabilize'

 -}
newtype StabilizeT monad a =
    StabilizeT { getStabilizeT :: MaybeT (StateT Bool monad) a }
    deriving (Functor, Applicative, Monad)

instance MonadTrans StabilizeT where
    lift = StabilizeT . Monad.lift . Monad.lift
    {-# INLINE lift #-}

instance MFunctor StabilizeT where
    hoist f = StabilizeT . within . getStabilizeT
      where
        within = Monad.hoist (Monad.hoist f)
    {-# INLINE hoist #-}

stable :: Monad monad => a -> StabilizeT monad a
stable a = StabilizeT $ do
    Monad.guard =<< Monad.State.get
    Monad.State.put False
    return a

unstable :: Monad monad => a -> StabilizeT monad a
unstable a = StabilizeT $ do
    Monad.State.put True
    return a

{- | Iterate the worker in a loop until it stabilizes.

The worker is stabilized when it calls 'stable' twice in succession, i.e. with
no intermediate call to 'unstable'.

 -}
stabilize
    :: Monad monad
    => (a -> StabilizeT monad a)  -- ^ Worker
    -> (a ->            monad a)
stabilize worker = flip evalStateT True . wrapper
  where
    wrapper a =
        getStabilizeT (worker a) & Error.maybeT (return a) wrapper
