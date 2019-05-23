{-|
Module      : Kore.Logger
Description : Logging functions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Logger
    ( LogMessage (..)
    , Severity (..)
    , Scope (..)
    , WithLog (..)
    , LogAction (..)
    , log
    , logDebug
    , logInfo
    , logWarning
    , logError
    , logCritical
    , withLogScope
    , liftLogAction
    , hoistLogAction
    ) where

import           Colog
                 ( LogAction (..) )
import qualified Control.Monad.Counter as Counter
import qualified Control.Monad.Except as Except
import qualified Control.Monad.Morph as Monad.Morph
import qualified Control.Monad.Reader as Reader
import qualified Control.Monad.RWS.Lazy as Monad.RWS.Lazy
import qualified Control.Monad.RWS.Strict as Monad.RWS.Strict
import qualified Control.Monad.State.Lazy as State.Lazy
import qualified Control.Monad.State.Strict as State.Strict
import qualified Control.Monad.State.Strict as Monad.State.Strict
import           Control.Monad.Trans
                 ( MonadTrans )
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Identity
                 ( IdentityT, runIdentityT )
import qualified Control.Monad.Trans.Maybe as Maybe
import qualified Control.Monad.Writer.Lazy as Writer.Lazy
import qualified Control.Monad.Writer.Strict as Writer.Strict
import           Data.Functor.Contravariant
                 ( contramap )
import           Data.String
                 ( IsString )
import           Data.Text
                 ( Text )
import           GHC.Stack
                 ( CallStack, HasCallStack, callStack )
import qualified Kore.Step.Transition as Transition
import           Prelude hiding
                 ( log )

import ListT
       ( ListT )

-- | Log level used to describe each log message. It is also used to set the
-- minimum level to be outputted.
data Severity
    = Debug
    -- ^ Lowest level used for low-level debugging.
    | Info
    -- ^ Used for various informative messages.
    | Warning
    -- ^ Used for odd/unusual cases which are recoverable.
    | Error
    -- ^ Used for application errors, unexpected behaviors, etc.
    | Critical
    -- ^ Used before shutting down the application.
    deriving (Show, Read, Eq, Ord)

-- | Logging scope, used by 'LogMessage'.
newtype Scope = Scope
    { unScope :: Text
    } deriving (Eq, Ord, Show, Semigroup, Monoid, IsString)

-- | This type should not be used directly, but rather should be created and
-- dispatched through the `log` functions.
data LogMessage = LogMessage
    { message   :: !Text
    -- ^ message being logged
    , severity  :: !Severity
    -- ^ log level / severity of message
    , scope     :: ![Scope]
    -- ^ scope of the message, usually of the form "a.b.c"
    , callstack :: !CallStack
    -- ^ call stack of the message, when available
    }

class Monad m => WithLog msg m where
    -- | Retrieve the 'LogAction' in scope.
    askLogAction :: m (LogAction m msg)

    -- | Modify the 'LogAction' over the scope of an action.
    withLog
        :: forall a
        .  (forall n. LogAction n msg -> LogAction n msg)
        -> m a
        -> m a

instance (WithLog msg m, Monad m) => WithLog msg (IdentityT m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog
        :: forall a
        .  (forall n. LogAction n msg -> LogAction n msg)
        -> IdentityT m a
        -> IdentityT m a
    withLog mapping =
        Monad.Trans.lift . withLog mapping . runIdentityT

instance (WithLog msg m, Monad m) => WithLog msg (Counter.CounterT m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = Counter.mapCounterT (withLog mapping)

instance (WithLog msg m, Monad m) => WithLog msg (Maybe.MaybeT m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = Maybe.mapMaybeT (withLog mapping)

instance (WithLog msg m, Monad m) => WithLog msg (Reader.ReaderT r m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = Reader.mapReaderT (withLog mapping)

instance (WithLog msg m, Monad m, Monoid w)
        => WithLog msg (Monad.RWS.Lazy.RWST r w s m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = Monad.RWS.Lazy.mapRWST (withLog mapping)

instance (WithLog msg m, Monad m, Monoid w)
        => WithLog msg (Monad.RWS.Strict.RWST r w s m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = Monad.RWS.Strict.mapRWST (withLog mapping)

instance (WithLog msg m, Monad m)
        => WithLog msg (State.Lazy.StateT s m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = State.Lazy.mapStateT (withLog mapping)

instance (WithLog msg m, Monad m)
        => WithLog msg (State.Strict.StateT s m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = State.Strict.mapStateT (withLog mapping)

instance (WithLog msg m, Monad m, Monoid w)
        => WithLog msg (Writer.Lazy.WriterT w m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = Writer.Lazy.mapWriterT (withLog mapping)

instance (WithLog msg m, Monad m, Monoid w)
        => WithLog msg (Writer.Strict.WriterT w m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = Writer.Strict.mapWriterT (withLog mapping)

instance (WithLog msg m, Monad m)
        => WithLog msg (Transition.TransitionT rule m) where
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    withLog mapping = Transition.mapTransitionT (withLog mapping)

-- | 'Monad.Trans.lift' any 'LogAction' into a monad transformer.
liftLogAction
    :: (Monad m, MonadTrans t)
    => LogAction m msg
    -> LogAction (t m) msg
liftLogAction logAction =
    Colog.LogAction (Monad.Trans.lift . Colog.unLogAction logAction)

-- | Use a natural transform on a 'LogAction'.
hoistLogAction
    :: (forall a. m a -> n a)
    -> LogAction m msg
    -> LogAction n msg
hoistLogAction f (LogAction logger) = LogAction $ \msg -> f (logger msg)

instance WithLog msg m => WithLog msg (Except.ExceptT e m) where
    askLogAction = Monad.Trans.lift (liftLogAction <$> askLogAction)
    withLog f = Monad.Morph.hoist (withLog f)

instance WithLog msg m => WithLog msg (ListT m) where
    askLogAction = Monad.Trans.lift (liftLogAction <$> askLogAction)
    withLog f = Monad.Morph.hoist (withLog f)

-- | Log any message.
logMsg :: WithLog msg m => msg -> m ()
logMsg msg = do
    logAction <- askLogAction
    Colog.unLogAction logAction msg

-- | Logs a message using given 'Severity'.
log
    :: forall m
    . (HasCallStack, WithLog LogMessage m)
    => Severity
    -- ^ If lower than the minimum severity, the message will not be logged
    -> Text
    -- ^ Message to be logged
    -> m ()
log s t = logMsg $ LogMessage t s mempty callStack

-- | Logs using 'Debug' log level. See 'log'.
logDebug
    :: forall m
    . (WithLog LogMessage m)
    => Text
    -> m ()
logDebug = log Debug

-- | Logs using 'Info' log level. See 'log'.
logInfo
    :: forall m
    . (WithLog LogMessage m)
    => Text
    -> m ()
logInfo = log Info

-- | Logs using 'Warning' log level. See 'log'.
logWarning
    :: forall m
    . (WithLog LogMessage m)
    => Text
    -> m ()
logWarning = log Warning

-- | Logs using 'Error' log level. See 'log'.
logError
    :: forall m
    . (WithLog LogMessage m)
    => Text
    -> m ()
logError = log Error

-- | Logs using 'Critical' log level. See 'log'.
logCritical
    :: forall m
    . (WithLog LogMessage m)
    => Text
    -> m ()
logCritical = log Critical

-- | Creates a new logging scope, appending the text to the current scope. For
-- example, if the current scope is "a.b" and 'withLogScope' is called with
-- "c", then the new scope will be "a.b.c".
withLogScope
    :: forall m a
    .  WithLog LogMessage m
    => Scope
    -- ^ new scope
    -> m a
    -- ^ continuation / enclosure for the new scope
    -> m a
withLogScope newScope = withLog (contramap appendScope)
  where
    appendScope (LogMessage msg sev scope callstack) =
        LogMessage msg sev (newScope : scope) callstack
