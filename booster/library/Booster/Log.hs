{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Booster.Log (
    module Booster.Log,
    -- re-export all log context patterns for convenience
    pattern CBooster,
    pattern CKore,
    pattern CProxy,
    pattern CExecute,
    pattern CSimplify,
    pattern CImplies,
    pattern CGetModel,
    pattern CAddModule,
    pattern CInternalise,
    pattern CMatch,
    pattern CDefinedness,
    pattern CConstraint,
    pattern CSMT,
    pattern CLlvm,
    pattern CCached,
    pattern CFailure,
    pattern CIndeterminate,
    pattern CAbort,
    pattern CSuccess,
    pattern CBreak,
    pattern CContinue,
    pattern CKoreTerm,
    pattern CDetail,
    pattern CSubstitution,
    pattern CDepth,
    pattern CError,
    pattern CWarn,
    pattern CInfo,
    pattern CRewrite,
    pattern CSimplification,
    pattern CFunction,
    pattern CCeil,
    pattern CTerm,
    pattern CHook,
) where

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
import Data.Aeson.Types (object)
import Data.Coerce (coerce)
import Data.Hashable qualified
import Data.List (foldl', intercalate, intersperse)
import Data.List.Extra (splitOn, takeEnd)
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text (Text, pack)
import Data.Text.Encoding (decodeUtf8)
import Prettyprinter (Pretty, pretty)
import System.Log.FastLogger (FormattedTime)
import UnliftIO (MonadUnliftIO)

import Booster.Definition.Attributes.Base
import Booster.Definition.Base (RewriteRule (..), SourceRef (..), sourceRef)
import Booster.Pattern.Base (
    Pattern (..),
    Predicate (..),
    Symbol (..),
    Term (..),
    TermAttributes (hash),
    pattern AndTerm,
 )
import Booster.Prettyprinter (renderOneLineText)
import Booster.Syntax.Json (KorePattern, addHeader, prettyPattern)
import Booster.Syntax.Json.Externalise (externaliseTerm)
import Booster.Util (Flag (..))
import Kore.JsonRpc.Types (rpcJsonConfig)
import Kore.JsonRpc.Types.ContextLog as CL

newtype Logger a = Logger (a -> IO ())

class ToLogFormat a where
    toTextualLog :: a -> Text
    toJSONLog :: a -> Value

instance ToLogFormat CLContext where
    toTextualLog = pack . show
    toJSONLog = toJSON

instance ToLogFormat Text where
    toTextualLog t = t
    toJSONLog t = String t

instance ToLogFormat Term where
    toTextualLog t = renderOneLineText $ pretty t
    toJSONLog t = toJSON $ addHeader $ externaliseTerm t

instance ToLogFormat (RewriteRule tag) where
    toTextualLog = shortRuleLocation
    toJSONLog = String . shortRuleLocation

shortRuleLocation :: RewriteRule tag -> Text
shortRuleLocation rule = renderOneLineText $
    pretty $
        case sourceRef rule of
            Located l@Location{file = FileSource f} ->
                Located l{file = FileSource $ "..." <> (intercalate "/" $ takeEnd 3 $ splitOn "/" f)}
            loc -> loc

data LogMessage where
    LogMessage :: ToLogFormat a => Flag "alwaysShown" -> [CLContext] -> a -> LogMessage

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

withContext :: LoggerMIO m => CLContext -> m a -> m a
withContext c =
    withLogger
        ( \(Logger l) -> Logger $ l . (\(LogMessage alwaysShown ctxt m) -> LogMessage alwaysShown (c : ctxt) m)
        )

withTermContext :: LoggerMIO m => Term -> m a -> m a
withTermContext t@(Term attrs _) m = withContext (CTerm $ Hex7 attrs.hash) $ do
    withContext CKoreTerm $ logMessage t
    m

withPatternContext :: LoggerMIO m => Pattern -> m a -> m a
withPatternContext Pattern{term, constraints} m =
    let t' = foldl' AndTerm term $ Set.toList $ Set.map coerce constraints -- FIXME
     in withTermContext t' m

instance ToLogFormat KorePattern where
    toTextualLog = prettyPattern
    toJSONLog p = toJSON p

withKorePatternContext :: LoggerMIO m => KorePattern -> m a -> m a
withKorePatternContext p m =
    withContext (CTerm (Hex7 h)) $ do
        withContext CKoreTerm $ logMessage p
        m
  where
    h = Data.Hashable.hash $ show p -- FIXME

withRuleContext ::
    ContextFor (RewriteRule tag) =>
    LoggerMIO m =>
    RewriteRule tag ->
    m a ->
    m a
withRuleContext rule m = withContext (contextFor rule) $ do
    withContext CDetail $ logPretty $ case sourceRef rule of
        Located Location{file = FileSource f, position} ->
            Located
                Location{file = FileSource $ "..." <> (intercalate "/" $ takeEnd 3 $ splitOn "/" f), position}
        loc -> loc
    m

class ContextFor a where
    contextFor :: a -> CLContext

instance ContextFor (RewriteRule "Rewrite") where
    contextFor = CRewrite . parseRuleId

instance ContextFor (RewriteRule "Function") where
    contextFor = CFunction . parseRuleId

instance ContextFor (RewriteRule "Simplification") where
    contextFor = CSimplification . parseRuleId

instance ContextFor (RewriteRule "Ceil") where
    contextFor = CCeil . parseRuleId

instance ContextFor Symbol where
    contextFor = CHook . (maybe "not-hooked" decodeUtf8) . (.attributes.hook)

parseRuleId :: RewriteRule tag -> CL.UniqueId
parseRuleId = fromMaybe CL.UNKNOWN . CL.parseUId . coerce . (.attributes.uniqueId)

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

textLogger :: ((Maybe FormattedTime -> Control.Monad.Logger.LogStr) -> IO ()) -> Logger LogMessage
textLogger l = Logger $ \(LogMessage _ ctxts msg) ->
    let logLevel = mconcat $ intersperse "][" $ map toTextualLog ctxts
     in l $ \mTime ->
            ( case mTime of
                Nothing -> mempty
                Just t -> Control.Monad.Logger.toLogStr t <> " "
            )
                <> "["
                <> (Control.Monad.Logger.toLogStr logLevel)
                <> "] "
                <> (Control.Monad.Logger.toLogStr $ toTextualLog msg)
                <> "\n"

jsonLogger :: ((Maybe FormattedTime -> Control.Monad.Logger.LogStr) -> IO ()) -> Logger LogMessage
jsonLogger l = Logger $ \(LogMessage _ ctxts msg) ->
    let ctxt = toJSON $ map toJSONLog ctxts
     in liftIO $
            l $ \mTime ->
                ( Control.Monad.Logger.toLogStr $
                    encodePretty' rpcJsonConfig{confIndent = Spaces 0} $
                        object $
                            ["context" .= ctxt, "message" .= toJSONLog msg]
                                <> case mTime of
                                    Nothing -> []
                                    Just t -> ["timestamp" .= decodeUtf8 t]
                )
                    <> "\n"

filterLogger :: (LogMessage -> Bool) -> Logger LogMessage -> Logger LogMessage
filterLogger p (Logger l) = Logger $ \m -> when (p m) $ l m
