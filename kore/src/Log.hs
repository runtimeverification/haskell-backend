{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Log
    (
    -- * Entries
      module Log.Entry
    , SomeEntry (..)
    -- * Interface
    , MonadLog (..)
    , WithLog
    -- * Implementation
    , LoggerT (..)
    -- * Log actions
    , LogAction (..)
    , liftLogAction
    , hoistLogAction
    , fromLogAction
    -- * Messages (Deprecated)
    , LogMessage (..)
    , log
    , logDebug
    , logInfo
    , logWarning
    , logError
    , logWith
    ) where

import Prelude.Kore

import Colog
    ( LogAction (..)
    , Severity (..)
    , cmap
    , (<&)
    )
import Control.Monad.Catch
    ( MonadCatch
    , MonadMask
    , MonadThrow
    )
import Control.Monad.Except
    ( ExceptT
    )
import Control.Monad.Morph
    ( MFunctor
    )
import qualified Control.Monad.Morph as Monad.Morph
import Control.Monad.Trans
    ( MonadTrans
    )
import Control.Monad.Trans.Accum
    ( AccumT
    , mapAccumT
    )
import Control.Monad.Trans.Identity
    ( IdentityT
    )
import Control.Monad.Trans.Maybe
    ( MaybeT
    )
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.State.Strict as Strict
    ( StateT
    )
import qualified Data.Sequence as Seq
import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified GHC.Stack as GHC

import Control.Monad.Counter
    ( CounterT
    )
import Log.Entry

-- | This type should not be used directly, but rather should be created and
-- dispatched through the `log` functions.
data LogMessage = LogMessage
    { message   :: Text
    -- ^ message being logged
    , severity  :: !Severity
    -- ^ log level / severity of message
    , callstack :: !GHC.CallStack
    -- ^ call stack of the message, when available
    }

instance Entry LogMessage where
    entrySeverity LogMessage { severity } = severity

instance Pretty LogMessage where
    pretty LogMessage { message, callstack } =
        Pretty.hsep
            [ Pretty.pretty message
            , Pretty.brackets (formatCallstack callstack)
            ]
      where
        formatCallstack :: GHC.CallStack -> Pretty.Doc ann
        formatCallstack cs
          | length (GHC.getCallStack cs) <= 1 = mempty
          | otherwise                         = callStackToBuilder cs
        callStackToBuilder :: GHC.CallStack -> Pretty.Doc ann
        callStackToBuilder =
            Pretty.pretty
            . GHC.prettyCallStack
            . GHC.popCallStack

type WithLog msg = MonadLog

-- | 'lift' any 'LogAction' into a monad transformer.
liftLogAction
    :: (Monad m, MonadTrans t)
    => LogAction m msg
    -> LogAction (t m) msg
liftLogAction logAction =
    Colog.LogAction (lift . Colog.unLogAction logAction)

-- | Use a natural transform on a 'LogAction'.
hoistLogAction
    :: (forall a. m a -> n a)
    -> LogAction m msg
    -> LogAction n msg
hoistLogAction f (LogAction logger) = LogAction $ \msg -> f (logger msg)

-- | Log any message.
logMsg :: (Entry msg, WithLog msg m) => msg -> m ()
logMsg = logEntry

-- | Logs a message using given 'Severity'.
log
    :: forall m
    . (HasCallStack, WithLog LogMessage m)
    => Severity
    -- ^ If lower than the minimum severity, the message will not be logged
    -> Text
    -- ^ Message to be logged
    -> m ()
log s t = logMsg $ LogMessage t s GHC.callStack

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

-- ---------------------------------------------------------------------
-- * LoggerT

class Monad m => MonadLog m where
    logEntry :: Entry entry => entry -> m ()
    default logEntry
        :: Entry entry
        => (MonadTrans trans, MonadLog log, m ~ trans log)
        => entry
        -> m ()
    logEntry = lift . logEntry
    {-# INLINE logEntry #-}

    logWhile :: Entry entry => entry -> m a -> m a
    default logWhile
        :: Entry entry
        => (MFunctor t, MonadLog log, m ~ t log)
        => entry
        -> m a
        -> m a
    logWhile entry = Monad.Morph.hoist $ logWhile entry

instance (Monoid acc, MonadLog log)
  => MonadLog (AccumT acc log) where
      logWhile = mapAccumT . logWhile

instance MonadLog log => MonadLog (CounterT log)

instance MonadLog log => MonadLog (ExceptT error log)

instance MonadLog log => MonadLog (IdentityT log)

instance MonadLog log => MonadLog (MaybeT log)

instance MonadLog log => MonadLog (ReaderT a log)

instance MonadLog log => MonadLog (Strict.StateT state log)

newtype LoggerT m a =
    LoggerT { getLoggerT :: ReaderT (LogAction m ActualEntry) m a }
    deriving (Functor, Applicative, Monad)
    deriving (MonadIO, MonadThrow, MonadCatch, MonadMask)

instance Monad m => MonadLog (LoggerT m) where
    logEntry entry = LoggerT $ do
        logAction <- ask
        let entryLogger = fromLogAction @ActualEntry logAction
        lift $ entryLogger <& toEntry entry

    logWhile entry2 action = do
        logEntry entry2
        LoggerT . local modifyContext $ getLoggerT action
      where
        modifyContext = Colog.cmap $ \entry1 ->
            entry1
                { entryContext =
                    entryContext entry1 <> Seq.singleton (toEntry entry2)
                }

instance MonadTrans LoggerT where
    lift = LoggerT . lift
    {-# INLINE lift #-}

logWith
    :: Entry entry
    => LogAction m ActualEntry
    -> entry
    -> m ()
logWith logger entry =
    fromLogAction @ActualEntry logger Colog.<& toEntry entry

fromLogAction :: forall a b m . From b a => LogAction m a -> LogAction m b
fromLogAction = cmap from
