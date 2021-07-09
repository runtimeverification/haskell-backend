{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Prof (
    MonadProf (..),
    defaultTraceProf,
) where

import Control.Monad.Catch (
    MonadMask,
    bracket_,
 )
import Control.Monad.RWS.Strict (
    RWST,
 )
import Control.Monad.Trans.Except (
    ExceptT,
 )
import Control.Monad.Trans.Reader (
    ReaderT,
 )
import qualified Control.Monad.Trans.State.Lazy as Lazy (
    StateT,
 )
import qualified Control.Monad.Trans.State.Strict as Strict (
    StateT,
 )
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import Debug.Trace.Text (
    traceEventIO,
 )
import Prelude.Kore

class Monad prof => MonadProf prof where
    -- | Attribute an action to a particular name for profiling.
    traceProf ::
        -- | name for profiling
        Text ->
        -- | action
        prof a ->
        prof a
    default traceProf ::
        MonadMask prof =>
        Text ->
        prof a ->
        prof a
    traceProf = defaultTraceProf
    {-# INLINE traceProf #-}

    -- | For internal use only.
    traceEvent :: Text -> prof ()

instance MonadProf IO where
    traceEvent = traceEventIO
    {-# INLINE traceEvent #-}

instance (MonadMask prof, MonadProf prof) => MonadProf (ExceptT e prof) where
    traceEvent name = lift (traceEvent name)
    {-# INLINE traceEvent #-}

instance (MonadMask prof, MonadProf prof) => MonadProf (ReaderT r prof) where
    traceEvent name = lift (traceEvent name)
    {-# INLINE traceEvent #-}

instance
    (MonadMask prof, MonadProf prof) =>
    MonadProf (Lazy.StateT s prof)
    where
    traceEvent name = lift (traceEvent name)
    {-# INLINE traceEvent #-}

instance
    (MonadMask prof, MonadProf prof) =>
    MonadProf (Strict.StateT s prof)
    where
    traceEvent name = lift (traceEvent name)
    {-# INLINE traceEvent #-}

instance
    (MonadMask prof, MonadProf prof) =>
    MonadProf (RWST r () s prof)
    where
    traceEvent name = lift (traceEvent name)
    {-# INLINE traceEvent #-}

defaultTraceProf ::
    (MonadProf prof, MonadMask prof) =>
    Text ->
    prof a ->
    prof a
defaultTraceProf name =
    bracket_ open close
  where
    open = traceEvent (Text.cons 'O' name)
    close = traceEvent (Text.cons 'C' name)
{-# INLINE defaultTraceProf #-}
