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
    , LoggerT (..)
    , SomeEntry (..)
    , withSomeEntry
    , Entry (..)
    , MonadLog (..)
    , mapLocalFunction
    ) where

import Colog
    ( LogAction (..)
    , (<&)
    )
import qualified Control.Monad.Except as Except
import Control.Monad.IO.Class
import Control.Monad.Morph
    ( MFunctor
    )
import qualified Control.Monad.Morph as Monad.Morph
import qualified Control.Monad.State.Strict as Strict
import Control.Monad.Trans
    ( MonadTrans
    )
import qualified Control.Monad.Trans as Monad.Trans
import Control.Monad.Trans.Accum
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Reader
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
    , getCallStack
    , popCallStack
    , prettyCallStack
    )
import Prelude hiding
    ( log
    )

import Control.Monad.Counter
import ListT
    ( ListT
    , mapListT
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
    , scope     :: ![Scope]
    -- ^ scope of the message, usually of the form "a.b.c"
    , callstack :: !CallStack
    -- ^ call stack of the message, when available
    }

instance Pretty.Pretty LogMessage where
    pretty LogMessage {message, severity, scope, callstack} =
        Pretty.hsep
            [ Pretty.brackets (Pretty.pretty severity)
            , Pretty.brackets (prettyScope scope)
            , ":"
            , Pretty.pretty message
            , Pretty.brackets (formatCallstack callstack)
            ]
      where
        prettyScope :: [Scope] -> Pretty.Doc ann
        prettyScope =
            mconcat
                . zipWith (<>) ("" : repeat ".")
                . fmap Pretty.pretty
        formatCallstack :: GHC.Stack.CallStack -> Pretty.Doc ann
        formatCallstack cs
          | length (getCallStack cs) <= 1 = mempty
          | otherwise                               = callStackToBuilder cs
        callStackToBuilder :: GHC.Stack.CallStack -> Pretty.Doc ann
        callStackToBuilder =
            Pretty.pretty
            . prettyCallStack
            . popCallStack

-- TODO (thomas.tuegel): Use TypeFamilies instead of MultiParamTypeClasses here.
class Monad m => WithLog msg m where
    -- | Retrieve the 'LogAction' in scope.
    askLogAction :: m (LogAction m msg)
    default askLogAction
        :: (MonadTrans t, WithLog msg n, m ~ t n) => m (LogAction m msg)
    askLogAction = liftLogAction <$> Monad.Trans.lift askLogAction
    {-# INLINE askLogAction #-}

    -- | Modify the 'LogAction' over the scope of an action.
    localLogAction
        :: (forall n. LogAction n msg -> LogAction n msg)
        -> m a
        -> m a
    default localLogAction
        :: (WithLog msg m', MFunctor t, m ~ t m')
        => (forall n. LogAction n msg -> LogAction n msg)
        -> m a
        -> m a
    localLogAction mapping = Monad.Morph.hoist (localLogAction mapping)
    {-# INLINE localLogAction #-}

instance (WithLog msg m, Monad m, Monoid w) => WithLog msg (AccumT w m) where
    localLogAction mapping = mapAccumT (localLogAction mapping)
    {-# INLINE localLogAction #-}

instance (WithLog msg m, Monad m) => WithLog msg (CounterT m)

instance (WithLog msg m, Monad m) => WithLog msg (IdentityT m)

instance (WithLog msg m, Monad m) => WithLog msg (MaybeT m)

instance (WithLog msg m, Monad m) => WithLog msg (ReaderT r m)

instance (WithLog msg m, Monad m) => WithLog msg (Strict.StateT s m)

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
    {-# INLINE askLogAction #-}

    localLogAction f = Monad.Morph.hoist (localLogAction f)
    {-# INLINE localLogAction #-}

instance WithLog msg m => WithLog msg (ListT m) where
    askLogAction = Monad.Trans.lift (liftLogAction <$> askLogAction)
    {-# INLINE askLogAction #-}

    localLogAction f = mapListT (localLogAction f)
    {-# INLINE localLogAction #-}

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
withLogScope newScope = localLogAction (contramap appendScope)
  where
    appendScope (LogMessage msg sev scope callstack) =
        LogMessage msg sev (newScope : scope) callstack

-- ---------------------------------------------------------------------
-- * LoggerT

class (Typeable entry, Pretty.Pretty entry) => Entry entry where
    toEntry :: entry -> SomeEntry
    toEntry = SomeEntry

    fromEntry :: SomeEntry -> Maybe entry
    fromEntry (SomeEntry entry) = Data.Typeable.cast entry

    shouldLog :: Severity -> Set Scope -> entry -> Bool

data SomeEntry where
    SomeEntry :: Entry entry => entry -> SomeEntry

instance Pretty.Pretty SomeEntry where
    pretty (SomeEntry entry) = Pretty.pretty entry

withSomeEntry
    :: (forall entry. Entry entry => entry -> a)
    -> SomeEntry
    -> a
withSomeEntry f (SomeEntry entry) = f entry

mapLocalFunction
    :: forall m
    .  (LogAction m LogMessage -> LogAction m LogMessage)
    -> LogAction m SomeEntry
    -> LogAction m SomeEntry
mapLocalFunction mapping la@(LogAction action) =
    LogAction $ \entry ->
        case fromEntry entry of
            Nothing -> action entry
            Just logMessage ->
                let LogAction f = mapping $ contramap toEntry la
                in f logMessage

instance Entry LogMessage where
    shouldLog :: Severity -> Set Scope -> LogMessage -> Bool
    shouldLog minSeverity currentScope LogMessage { severity, scope } =
        severity >= minSeverity && scope `member` currentScope
     where
       member :: [Scope] -> Set Scope -> Bool
       member s set
         | Set.null set = True
         | otherwise    = Fold.any (`Set.member` set) s

class Monad m => MonadLog m where
    logM :: Entry entry => entry -> m ()
    logScope :: Entry e1 => Entry e2 => (e1 -> e2) -> m a -> m a

newtype LoggerT m a =
    LoggerT { getLoggerT :: ReaderT (LogAction m SomeEntry) m a }
    deriving (Functor, Applicative, Monad)
    deriving (MonadIO)

instance Monad m => MonadLog (LoggerT m) where
    logM entry =
        LoggerT $ ask >>= Monad.Trans.lift . (<& toEntry entry)
    logScope f (LoggerT (ReaderT logActionReader)) =
        LoggerT . ReaderT
            $ \(LogAction logAction) ->
                logActionReader . LogAction
                    $ \entry ->
                        case fromEntry entry of
                            Nothing -> logAction entry
                            Just entry' -> logAction $ toEntry $ f entry'

instance Monad m => WithLog LogMessage (LoggerT m) where
    askLogAction :: LoggerT m (LogAction (LoggerT m) LogMessage)
    askLogAction = LoggerT . ReaderT $ pure . go
      where
        go :: LogAction m SomeEntry -> LogAction (LoggerT m) LogMessage
        go (LogAction fn) = LogAction $ Monad.Trans.lift . fn . toEntry
    {-# INLINE askLogAction #-}

    localLogAction
        :: (forall n. LogAction n LogMessage -> LogAction n LogMessage)
        -> LoggerT m a
        -> LoggerT m a
    localLogAction locally (LoggerT (ReaderT la)) =
        LoggerT . ReaderT $ la . mapLocalFunction locally
    {-# INLINE localLogAction #-}

instance MonadTrans LoggerT where
    lift = LoggerT . Monad.Trans.lift
    {-# INLINE lift #-}
