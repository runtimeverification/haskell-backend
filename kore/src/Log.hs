{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Log (
    -- * Entries
    module Log.Entry,
    SomeEntry (..),

    -- * Interface
    MonadLog (..),
    WithLog,

    -- * Implementation
    LoggerT (..),
    runLoggerT,
    askLogAction,

    -- * Log actions
    LogAction (..),
    liftLogAction,
    hoistLogAction,
    fromLogAction,

    -- * Messages (Deprecated)
    LogMessage (..),
    log,
    logDebug,
    logInfo,
    logWarning,
    logError,
    logWith,
) where

import Colog (
    LogAction (..),
    cmap,
    (<&),
 )
import qualified Control.Lens as Lens
import Control.Monad.Catch (
    MonadCatch,
    MonadMask,
    MonadThrow,
 )
import Control.Monad.Counter (
    CounterT,
 )
import Control.Monad.Except (
    ExceptT,
 )
import Control.Monad.Morph (
    MFunctor,
 )
import qualified Control.Monad.Morph as Monad.Morph
import Control.Monad.RWS.Strict (
    RWST,
 )
import Control.Monad.Trans.Accum (
    AccumT,
    mapAccumT,
 )
import Control.Monad.Trans.Identity (
    IdentityT,
 )
import Control.Monad.Trans.Maybe (
    MaybeT,
 )
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.State.Strict as Strict (
    StateT,
 )
import Data.Generics.Product (
    field,
 )
import Data.Text (
    Text,
 )
import qualified GHC.Generics as GHC
import qualified GHC.Stack as GHC
import Log.Entry
import Logic
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty
import Prof

{- | This type should not be used directly, but rather should be created and
 dispatched through the `log` functions.
-}
data LogMessage = LogMessage
    { -- | message being logged
      message :: Text
    , -- | log level / severity of message
      severity :: !Severity
    , -- | call stack of the message, when available
      callstack :: !GHC.CallStack
    }
    deriving stock (Show)

instance Entry LogMessage where
    entrySeverity LogMessage{severity} = severity

instance Pretty LogMessage where
    pretty LogMessage{message, callstack} =
        Pretty.hsep
            [ Pretty.pretty message
            , Pretty.brackets (formatCallstack callstack)
            ]
      where
        formatCallstack :: GHC.CallStack -> Pretty.Doc ann
        formatCallstack cs
            | length (GHC.getCallStack cs) <= 1 = mempty
            | otherwise = callStackToBuilder cs
        callStackToBuilder :: GHC.CallStack -> Pretty.Doc ann
        callStackToBuilder =
            Pretty.pretty
                . GHC.prettyCallStack
                . GHC.popCallStack

type WithLog msg = MonadLog

-- | 'lift' any 'LogAction' into a monad transformer.
liftLogAction ::
    (Monad m, MonadTrans t) =>
    LogAction m msg ->
    LogAction (t m) msg
liftLogAction logAction =
    Colog.LogAction (lift . Colog.unLogAction logAction)

-- | Use a natural transform on a 'LogAction'.
hoistLogAction ::
    (forall a. m a -> n a) ->
    LogAction m msg ->
    LogAction n msg
hoistLogAction f (LogAction logger) = LogAction $ \msg -> f (logger msg)

-- | Log any message.
logMsg :: (Entry msg, WithLog msg m) => msg -> m ()
logMsg = logEntry

-- | Logs a message using given 'Severity'.
log ::
    forall m.
    (HasCallStack, WithLog LogMessage m) =>
    -- | If lower than the minimum severity, the message will not be logged
    Severity ->
    -- | Message to be logged
    Text ->
    m ()
log s t = logMsg $ LogMessage t s GHC.callStack

-- | Logs using 'Debug' log level. See 'log'.
logDebug ::
    forall m.
    (WithLog LogMessage m) =>
    Text ->
    m ()
logDebug = log Debug

-- | Logs using 'Info' log level. See 'log'.
logInfo ::
    forall m.
    (WithLog LogMessage m) =>
    Text ->
    m ()
logInfo = log Info

-- | Logs using 'Warning' log level. See 'log'.
logWarning ::
    forall m.
    (WithLog LogMessage m) =>
    Text ->
    m ()
logWarning = log Warning

-- | Logs using 'Error' log level. See 'log'.
logError ::
    forall m.
    (WithLog LogMessage m) =>
    Text ->
    m ()
logError = log Error

-- ---------------------------------------------------------------------

-- * MonadLog

class Monad m => MonadLog m where
    logEntry :: Entry entry => entry -> m ()
    default logEntry ::
        Entry entry =>
        (MonadTrans trans, MonadLog log, m ~ trans log) =>
        entry ->
        m ()
    logEntry = lift . logEntry
    {-# INLINE logEntry #-}

    logWhile :: Entry entry => entry -> m a -> m a
    default logWhile ::
        Entry entry =>
        (MFunctor t, MonadLog log, m ~ t log) =>
        entry ->
        m a ->
        m a
    logWhile entry = Monad.Morph.hoist $ logWhile entry
    {-# INLINE logWhile #-}

instance (Monoid acc, MonadLog log) => MonadLog (AccumT acc log) where
    logWhile = mapAccumT . logWhile
    {-# INLINE logWhile #-}

instance MonadLog log => MonadLog (CounterT log)

instance MonadLog log => MonadLog (ExceptT error log)

instance MonadLog log => MonadLog (IdentityT log)

instance MonadLog log => MonadLog (LogicT log) where
    logWhile entry = mapLogicT (logWhile entry)
    {-# INLINE logWhile #-}

instance MonadLog log => MonadLog (MaybeT log)

instance MonadLog log => MonadLog (ReaderT a log)

instance MonadLog log => MonadLog (Strict.StateT state log)

instance MonadLog log => MonadLog (RWST a () state log)

-- ---------------------------------------------------------------------

-- * LoggerT

newtype LoggerT m a = LoggerT {getLoggerT :: ReaderT (LoggerEnv m) m a}
    deriving newtype (Functor, Applicative, Monad)
    deriving newtype (MonadIO, MonadThrow, MonadCatch, MonadMask)

data LoggerEnv monad = LoggerEnv
    { logAction :: !(LogAction monad ActualEntry)
    , context :: ![SomeEntry]
    }
    deriving stock (GHC.Generic)

askLogAction :: Monad m => LoggerT m (LogAction m SomeEntry)
askLogAction = LoggerT $ do
    LoggerEnv{logAction, context = entryContext} <- ask
    let mkActualEntry actualEntry = ActualEntry{actualEntry, entryContext}
    pure (Colog.cmap mkActualEntry logAction)
{-# INLINE askLogAction #-}

runLoggerT ::
    LoggerT monad a ->
    LogAction monad ActualEntry ->
    monad a
runLoggerT LoggerT{getLoggerT} logAction =
    runReaderT getLoggerT LoggerEnv{logAction, context = mempty}
{-# INLINE runLoggerT #-}

instance Monad m => MonadLog (LoggerT m) where
    logEntry entry = do
        someLogAction <- askLogAction
        lift $ someLogAction <& toEntry entry
    {-# INLINE logEntry #-}

    logWhile entry2 action = do
        logEntry entry2
        LoggerT . addContext $ getLoggerT action
      where
        addContext = local $ Lens.over (field @"context") (toEntry entry2 :)
    {-# INLINE logWhile #-}

instance MonadTrans LoggerT where
    lift = LoggerT . lift
    {-# INLINE lift #-}

instance (MonadMask prof, MonadProf prof) => MonadProf (LoggerT prof) where
    traceEvent name = lift (traceEvent name)
    {-# INLINE traceEvent #-}

logWith ::
    Entry entry =>
    LogAction m SomeEntry ->
    entry ->
    m ()
logWith logger entry = logger Colog.<& toEntry entry
{-# INLINE logWith #-}

fromLogAction :: forall a b m. From b a => LogAction m a -> LogAction m b
fromLogAction = cmap from
{-# INLINE fromLogAction #-}
