module Kore.Network.JSONRPC where

import Control.Monad.Logger (MonadLoggerIO)
import Control.Monad.Reader (runReaderT)
import Data.Aeson (ToJSON)
import Data.Aeson.Encode.Pretty as Json
import Data.ByteString (ByteString)
import Data.ByteString.Lazy.Char8 qualified as L8
import Data.Conduit (ConduitT, Void, runConduit, (.|))
import Data.Conduit.List qualified as CL
import Data.Conduit.TMChan (closeTBMChan, sinkTBMChan, sourceTBMChan)
import Data.Conduit.Network (ServerSettings, runGeneralTCPServer, appSink, appSource)
import Network.JSONRPC(JSONRPCT, Session(..), Ver, decodeConduit, initSession, processIncoming)
import Prelude.Kore
import UnliftIO (MonadUnliftIO, atomically, withAsync, wait)

-- Conduit to encode JSON to ByteString.
encodeConduit :: (ToJSON j, Monad m) => Json.Config -> ConduitT j ByteString m ()
encodeConduit encodeOpts = CL.mapM $ \m -> return . L8.toStrict $ encodePretty' encodeOpts m

-- | Create JSON-RPC session around conduits from transport layer.  When
-- context exits session disappears.
runJSONRPCT ::
       (MonadLoggerIO m, MonadUnliftIO m)
    => Json.Config -- ^ aeson-pretty Config
    -> Ver -- ^ JSON-RPC version
    -> Bool -- ^ Ignore incoming requests/notifs
    -> ConduitT ByteString Void m () -- ^ Sink to send messages
    -> ConduitT () ByteString m () -- ^ Source to receive messages from
    -> JSONRPCT m a -- ^ JSON-RPC action
    -> m a -- ^ Output of action
runJSONRPCT encodeOpts ver ignore snk src f = do
    qs <- liftIO . atomically $ initSession ver ignore
    let inSnk  = sinkTBMChan (inCh qs)
        outSrc = sourceTBMChan (outCh qs)
    withAsync (runConduit $ src .| decodeConduit ver .| inSnk) $ const $
        withAsync (runConduit $ outSrc .| encodeConduit encodeOpts .| snk) $ \o ->
            withAsync (runReaderT processIncoming qs) $ const $ do
                a <- runReaderT f qs
                liftIO $ do
                    atomically . closeTBMChan $ outCh qs
                    _ <- wait o
                    return a


-- | TCP server transport for JSON-RPC.
jsonrpcTCPServer
    :: (MonadLoggerIO m, MonadUnliftIO m)
    => Json.Config     -- ^ aeson-pretty Config
    -> Ver             -- ^ JSON-RPC version
    -> Bool            -- ^ Ignore incoming requests or notifications
    -> ServerSettings  -- ^ Connection settings
    -> JSONRPCT m ()   -- ^ Action to perform on connecting client thread
    -> m a
jsonrpcTCPServer encodeOpts ver ignore ss f = runGeneralTCPServer ss $ \cl ->
    runJSONRPCT encodeOpts{Json.confTrailingNewline = True} ver ignore (appSink cl) (appSource cl) f
