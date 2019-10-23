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
    , WithLog
    , WithScope (..)
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
    , LoggerT (..)
    , SomeEntry (..)
    , someEntry
    , withSomeEntry
    , Entry (..)
    , defaultShouldLog
    , MonadLog (..)
    ) where

import Colog
    ( LogAction (..)
    , (<&)
    )
import qualified Control.Lens as Lens
import Control.Lens.Prism
    ( Prism
    )
import Control.Monad.Except
    ( ExceptT
    )
import qualified Control.Monad.Except as Except
import Control.Monad.IO.Class
import Control.Monad.Morph
    ( MFunctor
    )
import qualified Control.Monad.Morph as Morph
import Control.Monad.Trans
    ( MonadTrans
    )
import qualified Control.Monad.Trans as Monad.Trans
import Control.Monad.Trans.Accum
    ( AccumT
    )
import qualified Control.Monad.Trans.Accum as Accum
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
import qualified Data.Foldable as Fold
import Data.Functor.Contravariant
    ( contramap
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.String
    ( IsString
    )
import Data.Text
    ( Text
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )
import qualified Data.Typeable
    ( cast
    )
import GHC.Stack
    ( CallStack
    , HasCallStack
    , callStack
    )
import Prelude hiding
    ( log
    )

import Control.Monad.Counter
    ( CounterT
    )

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

instance Pretty.Pretty Severity where
    pretty = Pretty.pretty . show

-- | Logging scope, used by 'LogMessage'.
newtype Scope = Scope
    { unScope :: Text
    } deriving (Eq, Ord, Read, Show, Semigroup, Monoid, IsString)

instance Pretty.Pretty Scope where
    pretty = Pretty.pretty . unScope

-- | This type should not be used directly, but rather should be created and
-- dispatched through the `log` functions.
data LogMessage = LogMessage
    { message   :: !Text
    -- ^ message being logged
    , severity  :: !Severity
    -- ^ log level / severity of message
    , callstack :: !CallStack
    -- ^ call stack of the message, when available
    }

type WithLog msg = MonadLog

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

-- | Log any message.
logMsg :: (Entry msg, WithLog msg m) => msg -> m ()
logMsg = logM

-- | Logs a message using given 'Severity'.
log
    :: forall m
    . (HasCallStack, WithLog LogMessage m)
    => Severity
    -- ^ If lower than the minimum severity, the message will not be logged
    -> Text
    -- ^ Message to be logged
    -> m ()
log s t = logMsg $ LogMessage t s callStack

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

data WithScope = WithScope
    { entry :: SomeEntry
    , scope :: Scope
    } deriving Typeable

instance Entry WithScope where
    shouldLog
        minSeverity
        currentScope
        WithScope { entry = SomeEntry entry, scope }
      = scope `Set.member` currentScope
        || shouldLog minSeverity currentScope entry

    toLogMessage WithScope { entry = SomeEntry entry } = toLogMessage entry

withLogScope
    :: forall m a
    .  WithLog LogMessage m
    => Scope
    -- ^ new scope
    -> m a
    -- ^ continuation / enclosure for the new scope
    -> m a
withLogScope newScope =
    logScope appendScope
  where
    appendScope entry =
        toEntry $ WithScope entry newScope

-- ---------------------------------------------------------------------
-- * LoggerT

class Typeable entry => Entry entry where
    toEntry :: entry -> SomeEntry
    toEntry = SomeEntry

    fromEntry :: SomeEntry -> Maybe entry
    fromEntry (SomeEntry entry) = Data.Typeable.cast entry

    shouldLog :: Severity -> Set Scope -> entry -> Bool

    toLogMessage :: entry -> LogMessage

instance Entry LogMessage where
    -- TODO(Vladimir): this probably needs reviewed
    shouldLog :: Severity -> Set Scope -> LogMessage -> Bool
    shouldLog minSeverity _ LogMessage { severity } = severity >= minSeverity

    toLogMessage :: LogMessage -> LogMessage
    toLogMessage = id

defaultShouldLog :: Severity -> [Scope] -> Severity -> Set Scope -> Bool
defaultShouldLog severity scope minSeverity currentScope =
    severity >= minSeverity && scope `member` currentScope
  where
    member :: [Scope] -> Set Scope -> Bool
    member s set
      | Set.null set = True
      | otherwise    = Fold.any (`Set.member` set) s

someEntry :: (Entry e1, Entry e2) => Prism SomeEntry SomeEntry e1 e2
someEntry = Lens.prism' toEntry fromEntry

data SomeEntry where
    SomeEntry :: Entry entry => entry -> SomeEntry

withSomeEntry
    :: (forall entry. Entry entry => entry -> a)
    -> SomeEntry
    -> a
withSomeEntry f (SomeEntry entry) = f entry

class Monad m => MonadLog m where
    logM :: Entry entry => entry -> m ()
    default logM
        :: Entry entry
        => (MonadTrans trans, MonadLog log, m ~ trans log)
        => entry
        -> m ()
    logM = Monad.Trans.lift . logM
    {-# INLINE logM #-}

    logScope :: (SomeEntry -> SomeEntry) -> m a -> m a
    default logScope
        :: (MFunctor trans, MonadLog log, m ~ trans log)
        => (SomeEntry -> SomeEntry)
        -> m a
        -> m a
    logScope locally = Morph.hoist (logScope locally)
    {-# INLINE logScope #-}

instance (Monoid acc, MonadLog log) => MonadLog (AccumT acc log) where
    logScope locally = Accum.mapAccumT (logScope locally)
    {-# INLINE logScope #-}

instance MonadLog log => MonadLog (CounterT log)

instance MonadLog log => MonadLog (ExceptT error log)

instance MonadLog log => MonadLog (IdentityT log)

instance MonadLog log => MonadLog (MaybeT log)

instance MonadLog log => MonadLog (Strict.StateT state log)

newtype LoggerT m a =
    LoggerT { getLoggerT :: ReaderT (LogAction m SomeEntry) m a }
    deriving (Functor, Applicative, Monad)
    deriving (MonadIO)

instance Monad m => MonadLog (LoggerT m) where
    logM entry =
        LoggerT $ ask >>= Monad.Trans.lift . (<& toEntry entry)
    logScope f = LoggerT . local (contramap f) . getLoggerT

instance MonadTrans LoggerT where
    lift = LoggerT . Monad.Trans.lift
    {-# INLINE lift #-}

