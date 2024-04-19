{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Booster.Log where
import Data.Functor.Contravariant
import Data.Text(Text, pack)
import Data.Aeson((.=), object, Value (String), ToJSON (toJSON))
import Control.Monad.IO.Class


import Booster.Pattern.Base(Term(..), TermAttributes(hash))
import Numeric (showHex)
import Booster.Prettyprinter (renderOneLineText)
import Prettyprinter (pretty)
import Booster.Syntax.Json.Externalise (externaliseTerm)
import Data.String (IsString)
import Booster.Syntax.Json (KorePattern, prettyPattern)
import qualified Data.Hashable
import qualified Control.Monad.Trans.Class as Trans
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Reader (ReaderT (..), withReaderT, ask, withReader)
import Control.Monad.Trans.State (StateT (..), get, put, evalStateT)
import Control.Monad.Logger (MonadLoggerIO (askLoggerIO), MonadLogger, logWithoutLoc, LogLevel (..), logInfoN, defaultLoc, ToLogStr (toLogStr))
import qualified Control.Monad.Trans.State.Strict as Strict

newtype Logger a = Logger (a -> IO ())

instance Contravariant Logger where
  contramap f (Logger t) = Logger (t . f)


class ToLogFormat a where
  toTextualLog :: a -> Text
  -- toJSONLog :: a -> Value


data LogContext = forall a. ToLogFormat a => LogContext a



data LogMessage where
  LogMessage :: ToLogFormat a => [LogContext] -> a -> LogMessage



class MonadLoggerIO m => LoggerMIO m where
  getLogger :: m (Logger LogMessage)
  default getLogger :: (Trans.MonadTrans t, LoggerMIO n, m ~ t n) => m (Logger LogMessage)
  getLogger = Trans.lift getLogger

  withLogger :: (Logger LogMessage -> Logger LogMessage) -> m a -> m a

instance LoggerMIO m => LoggerMIO (MaybeT m) where
  withLogger modL (MaybeT m) = MaybeT $ withLogger modL m
instance LoggerMIO m => LoggerMIO (ExceptT e m) where
  withLogger modL (ExceptT m) = ExceptT $ withLogger modL m
instance LoggerMIO m => LoggerMIO (ReaderT r m) where
  withLogger modL (ReaderT m) = ReaderT $ \r -> withLogger modL $ m r
instance LoggerMIO m => LoggerMIO (StateT s m) where
  withLogger modL (StateT m) = StateT $ \s -> withLogger modL $ m s
instance LoggerMIO m => LoggerMIO (Strict.StateT s m) where
  withLogger modL (Strict.StateT m) = Strict.StateT $ \s -> withLogger modL $ m s


logMessage :: (LoggerMIO m, ToLogFormat a) => a -> m ()
logMessage a = getLogger >>= \case
  (Logger l) -> liftIO $ l $ LogMessage [] a


withContext :: LoggerMIO m => LogContext -> m a -> m a
withContext c = withLogger (\(Logger l) -> Logger $ l . (\(LogMessage ctxt m) -> LogMessage (c:ctxt) m))



newtype TermCtxt = TermCtxt Int

instance ToLogFormat TermCtxt where
  toTextualLog (TermCtxt hsh) = "term " <> (pack $ showHex hsh "")
  -- toJSONLog (TermCtxt hsh) = object [ "term" .= hsh ]

instance ToLogFormat Term where
  toTextualLog t = renderOneLineText $ pretty t
  -- toJSONLog t = toJSON $ externaliseTerm t


instance ToLogFormat Text where
  toTextualLog t = t
  -- toJSONLog t = String t

withTermContext :: LoggerMIO m => Term -> m a -> m a
withTermContext t@(Term attrs _) m = withContext (LogContext $ TermCtxt attrs.hash) $ do
  logMessage t
  m


instance ToLogFormat KorePattern where
  toTextualLog = prettyPattern


newtype KorePatternCtxt = KorePatternCtxt KorePattern


instance ToLogFormat KorePatternCtxt where
    toTextualLog (KorePatternCtxt t) = "kore term " <> (pack $ showHex (Data.Hashable.hash $ prettyPattern t) "")
 


withKorePatternContext :: LoggerMIO m => KorePattern -> m a -> m a
withKorePatternContext t m = withContext (LogContext $ KorePatternCtxt t) $ do
  logMessage t
  m



newtype LoggerT m a = LoggerT {unLoggerT :: ReaderT (Logger LogMessage) m a}
  deriving newtype (Applicative, Functor, Monad, MonadIO, MonadLogger, MonadLoggerIO)

instance MonadLoggerIO m => LoggerMIO (LoggerT m) where
  getLogger = LoggerT ask
  withLogger modL (LoggerT m) = LoggerT $ withReaderT modL m

runLogger :: MonadLoggerIO m => LoggerT m a -> m a
runLogger (LoggerT m) = do
  l <- askLoggerIO
  runReaderT m $ Logger $ \(LogMessage ctxts msg) -> l defaultLoc "" LevelInfo $ toLogStr $ (mconcat $ map (\(LogContext l) -> "[" <> toTextualLog l <> "]") ctxts) <> " " <> toTextualLog msg