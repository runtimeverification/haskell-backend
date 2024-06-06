{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Booster.Log (module Booster.Log) where

import Control.Monad (when)
import Control.Monad.IO.Class
import Control.Monad.Logger qualified
import Control.Monad.Trans.Class qualified as Trans
import Control.Monad.Trans.Except (ExceptT (..))
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Reader (ReaderT (..), ask, withReaderT)
import Control.Monad.Trans.State (StateT (..))
import Control.Monad.Trans.State.Strict qualified as Strict
import Data.Aeson (ToJSON (..), Value (..), (.=))
import Data.Aeson.Encode.Pretty (Config (confIndent), Indent (Spaces), encodePretty')
import Data.Aeson.Key qualified as Key
import Data.Aeson.Types (object)
import Data.Coerce (coerce)
import Data.Data (Proxy (..))
import Data.Hashable qualified
import Data.List (foldl', intercalate, intersperse)
import Data.List.Extra (splitOn, takeEnd)
import Data.Set qualified as Set
import Data.String (IsString)
import Data.Text (Text, pack)
import Data.Text.Lazy qualified as LazyText
import GHC.Exts (IsString (..))
import GHC.TypeLits (KnownSymbol, symbolVal)
import Prettyprinter (Pretty, pretty)

import Booster.Definition.Attributes.Base
import Booster.Definition.Base (RewriteRule (..), SourceRef (..), sourceRef)
import Booster.Pattern.Base (
    Pattern (..),
    Predicate (..),
    Term (..),
    TermAttributes (hash),
    pattern AndTerm,
 )
import Booster.Prettyprinter (renderOneLineText)
import Booster.Syntax.Json (KorePattern, addHeader, prettyPattern)
import Booster.Syntax.Json.Externalise (externaliseTerm)
import Booster.Util (Flag (..))
import Kore.JsonRpc.Types (rpcJsonConfig)
import Kore.Util (showHashHex)
import UnliftIO (MonadUnliftIO)

newtype Logger a = Logger (a -> IO ())

class ToLogFormat a where
    toTextualLog :: a -> Text
    toJSONLog :: a -> Value

data LogContext = forall a. ToLogFormat a => LogContext a

instance IsString LogContext where
    fromString = LogContext . pack

data LogMessage where
    LogMessage :: ToLogFormat a => Flag "alwaysShown" -> [LogContext] -> a -> LogMessage

class MonadIO m => LoggerMIO m where
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

instance MonadIO m => LoggerMIO (Control.Monad.Logger.NoLoggingT m) where
    getLogger = pure $ Logger $ \_ -> pure ()
    withLogger _ = id

logMessage :: (LoggerMIO m, ToLogFormat a) => a -> m ()
logMessage a =
    getLogger >>= \case
        (Logger l) -> liftIO $ l $ LogMessage (Flag False) [] a

{- Log message which is always shown even when context filters are applied -}
logMessage' :: (LoggerMIO m, ToLogFormat a) => a -> m ()
logMessage' a =
    getLogger >>= \case
        (Logger l) -> liftIO $ l $ LogMessage (Flag True) [] a

logPretty :: (LoggerMIO m, Pretty a) => a -> m ()
logPretty = logMessage . renderOneLineText . pretty

withContext :: LoggerMIO m => LogContext -> m a -> m a
withContext c =
    withLogger
        ( \(Logger l) -> Logger $ l . (\(LogMessage alwaysShown ctxt m) -> LogMessage alwaysShown (c : ctxt) m)
        )

newtype TermCtxt = TermCtxt Int

instance ToLogFormat TermCtxt where
    toTextualLog (TermCtxt hsh) = "term " <> (showHashHex hsh)
    toJSONLog (TermCtxt hsh) = object ["term" .= showHashHex hsh]

newtype HookCtxt = HookCtxt Text

instance ToLogFormat HookCtxt where
    toTextualLog (HookCtxt h) = "hook " <> h
    toJSONLog (HookCtxt h) = object ["hook" .= h]

instance ToLogFormat Term where
    toTextualLog t = renderOneLineText $ pretty t
    toJSONLog t = toJSON $ addHeader $ externaliseTerm t

instance ToLogFormat Text where
    toTextualLog t = t
    toJSONLog t = String t

withTermContext :: LoggerMIO m => Term -> m a -> m a
withTermContext t@(Term attrs _) m = withContext (LogContext $ TermCtxt attrs.hash) $ do
    withContext "kore-term" $ logMessage t
    m

withPatternContext :: LoggerMIO m => Pattern -> m a -> m a
withPatternContext Pattern{term, constraints} m =
    let t' = foldl' AndTerm term $ Set.toList $ Set.map coerce constraints
     in withTermContext t' m

instance ToLogFormat KorePattern where
    toTextualLog = prettyPattern
    toJSONLog p = toJSON p

newtype KorePatternCtxt = KorePatternCtxt KorePattern

instance ToLogFormat KorePatternCtxt where
    toTextualLog (KorePatternCtxt t) = "term " <> (showHashHex $ Data.Hashable.hash $ prettyPattern t)
    toJSONLog (KorePatternCtxt t) = object ["term" .= (showHashHex $ Data.Hashable.hash $ prettyPattern t)]

instance KnownSymbol k => ToLogFormat (RewriteRule k) where
    toTextualLog RewriteRule{attributes} =
        LazyText.toStrict $
            (LazyText.toLower $ LazyText.pack $ symbolVal (Proxy :: Proxy k))
                <> " "
                <> (LazyText.take 7 . LazyText.fromStrict . coerce $ attributes.uniqueId)
    toJSONLog RewriteRule{attributes} =
        object
            [ (Key.fromText $ LazyText.toStrict $ LazyText.toLower $ LazyText.pack $ symbolVal (Proxy :: Proxy k))
                .= (coerce attributes.uniqueId :: Text)
            ]

withKorePatternContext :: LoggerMIO m => KorePattern -> m a -> m a
withKorePatternContext t m = withContext (LogContext $ KorePatternCtxt t) $ do
    withContext "kore-term" $ logMessage t
    m

withRuleContext :: KnownSymbol tag => LoggerMIO m => RewriteRule tag -> m a -> m a
withRuleContext rule m = withContext (LogContext rule) $ do
    withContext "detail" $ logPretty $ case sourceRef rule of
        Located Location{file = FileSource f, position} ->
            Located
                Location{file = FileSource $ "..." <> (intercalate "/" $ takeEnd 3 $ splitOn "/" f), position}
        loc -> loc
    m

data WithJsonMessage where
    WithJsonMessage :: ToLogFormat a => Value -> a -> WithJsonMessage

instance ToLogFormat WithJsonMessage where
    toTextualLog (WithJsonMessage _ a) = toTextualLog a
    toJSONLog (WithJsonMessage v _) = v

newtype LoggerT m a = LoggerT {unLoggerT :: ReaderT (Logger LogMessage) m a}
    deriving newtype
        ( Applicative
        , Functor
        , Monad
        , MonadIO
        , Control.Monad.Logger.MonadLogger
        , Control.Monad.Logger.MonadLoggerIO
        , MonadUnliftIO
        )

instance MonadIO m => LoggerMIO (LoggerT m) where
    getLogger = LoggerT ask
    withLogger modL (LoggerT m) = LoggerT $ withReaderT modL m

textLogger :: (Control.Monad.Logger.LogStr -> IO ()) -> Logger LogMessage
textLogger l = Logger $ \(LogMessage _ ctxts msg) ->
    let logLevel = mconcat $ intersperse "][" $ map (\(LogContext lc) -> toTextualLog lc) ctxts
     in l $
            "["
                <> (Control.Monad.Logger.toLogStr logLevel)
                <> "] "
                <> (Control.Monad.Logger.toLogStr $ toTextualLog msg)
                <> "\n"

jsonLogger :: (Control.Monad.Logger.LogStr -> IO ()) -> Logger LogMessage
jsonLogger l = Logger $ \(LogMessage _ ctxts msg) ->
    let ctxt = toJSON $ map (\(LogContext lc) -> toJSONLog lc) ctxts
     in liftIO $
            l $
                ( Control.Monad.Logger.toLogStr $
                    encodePretty' rpcJsonConfig{confIndent = Spaces 0} $
                        object ["context" .= ctxt, "message" .= toJSONLog msg]
                )
                    <> "\n"

filterLogger :: (LogMessage -> Bool) -> Logger LogMessage -> Logger LogMessage
filterLogger p (Logger l) = Logger $ \m -> when (p m) $ l m
