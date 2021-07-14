{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
This module should be imported qualified:
@
import qualified Kore.Rewrite.Function.Memo as Memo
@
-}
module Kore.Rewrite.Function.Memo (
    Self (..),
    CacheKey,
    Cache,
    forgetful,
    simple,
    liftSelf,
    new,
) where

import Control.Monad.State.Class (
    MonadState,
 )
import qualified Control.Monad.State.Class as State
import Control.Monad.State.Strict (
    State,
    runState,
 )
import Data.HashMap.Strict (
    HashMap,
 )
import qualified Data.HashMap.Strict as HashMap
import Data.IORef
import qualified Data.Tuple as Tuple
import Kore.Internal.TermLike
import Prelude.Kore

-- | A function application memoizer.
data Self monad = Self
    { recall ::
        Application Symbol (TermLike Concrete) ->
        monad (Maybe (TermLike Concrete))
    , record ::
        Application Symbol (TermLike Concrete) ->
        TermLike Concrete ->
        monad ()
    }

{- | The forgetful memoizer.

@forgetful@ recalls nothing and records nothing.
-}
forgetful :: Applicative monad => Self monad
forgetful = Self{recall = \_ -> pure Nothing, record = \_ _ -> pure ()}

-- | The concrete function pattern used as a @Key@ into the memoization cache.
type CacheKey = Application Symbol (TermLike Concrete)

-- | The memoization @Cache@.
type Cache = HashMap CacheKey (TermLike Concrete)

{- | The simple memoizer.

@simple@ uses a simple 'State' monad for state tracking.
-}
simple :: MonadState Cache state => Self state
simple =
    Self{recall, record}
  where
    recall application = State.gets $ HashMap.lookup application
    record application result =
        State.modify' $ HashMap.insert application result

-- | Transform a memoizer using the provided morphism.
liftSelf ::
    (forall x. m x -> n x) ->
    (Self m -> Self n)
liftSelf lifting delegate =
    Self
        { recall = \application ->
            lifting $ recall delegate application
        , record = \application result ->
            lifting $ record delegate application result
        }

{- | Create a new memoizer.

(The memoizer's state is encapsulated in a mutable reference.)
-}
new :: forall io. MonadIO io => io (Self io)
new = do
    ref <- liftIO $ newIORef HashMap.empty
    let runStateRef :: State Cache a -> io a
        runStateRef state =
            (liftIO . atomicModifyIORef' ref) (Tuple.swap . runState state)
    return (liftSelf runStateRef simple)
