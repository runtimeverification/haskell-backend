{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-partial-fields #-}

module Kore.Trace (module Kore.Trace) where

import Control.Monad (when)
import Control.Monad.Catch (MonadMask, bracket_)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Binary (Binary (get, put), Get, Put, Word32, get)
import Data.Binary.Get (getByteString)
import Data.Binary.Put (putByteString, runPut)
import Data.Bits
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.IORef
import Data.Kind (Type)
import Debug.Trace.Binary (traceBinaryEvent, traceBinaryEventIO)
import Debug.Trace.Flags
import GHC.IO (unsafePerformIO)

type family Sum a :: Type where
    Sum '[] = ()
    Sum (a ': as) = Either a (Sum as)

data CustomUserEventType = Timing | LlvmCalls deriving (Show, Enum, Read, Bounded)

class CustomUserEvent e where
    encodeUserEvent :: e -> Put
    decodeUserEvent :: Get e
    userEventTag :: proxy e -> ByteString
    eventType :: proxy e -> CustomUserEventType

class DecodeUserEvents es where
    decodeUserEvents' :: ByteString -> Get (Sum es)

instance DecodeUserEvents '[] where
    decodeUserEvents' _tag = pure ()

instance (CustomUserEvent e, DecodeUserEvents es) => DecodeUserEvents (e ': es) where
    decodeUserEvents' tag =
        if userEventTag (undefined :: proxy e) == tag
            then Left <$> decodeUserEvent @e
            else Right <$> decodeUserEvents' @es tag

decodeCustomUserEvent :: forall es. DecodeUserEvents es => Get (Sum es)
decodeCustomUserEvent = getByteString 5 >>= decodeUserEvents' @es

enabledCustomUserEventTypes :: IORef Word32
{-# NOINLINE enabledCustomUserEventTypes #-}
enabledCustomUserEventTypes = unsafePerformIO $ newIORef 0

enableCustomUserEvent :: Enum a => a -> IO ()
enableCustomUserEvent a =
    modifyIORef enabledCustomUserEventTypes (.|. (bit $ fromEnum a))

customUserEventEnabled :: Enum a => a -> Bool
customUserEventEnabled a =
    unsafePerformIO $
        flip testBit (fromEnum a) <$> readIORef enabledCustomUserEventTypes

newtype Start = Start ByteString

instance CustomUserEvent Start where
    encodeUserEvent (Start ident) = put ident
    decodeUserEvent = Start <$> get
    userEventTag _ = "START"
    eventType _ = Timing

newtype Stop = Stop ByteString

instance CustomUserEvent Stop where
    encodeUserEvent (Stop ident) = put ident
    decodeUserEvent = Stop <$> get
    userEventTag _ = "STOP "
    eventType _ = Timing

encodeCustomUserEvent :: forall e. CustomUserEvent e => e -> Put
encodeCustomUserEvent e = do
    putByteString $ userEventTag (undefined :: proxy e)
    encodeUserEvent e

traceIO :: forall m e. MonadIO m => CustomUserEvent e => e -> m ()
traceIO e
    | userTracingEnabled && customUserEventEnabled (eventType (undefined :: proxy e)) = do
        let message = BL.toStrict $ runPut $ encodeCustomUserEvent e
        when (BS.length message > 2 ^ (16 :: Int)) $ error "eventlog message too long"
        liftIO $ traceBinaryEventIO message
    | otherwise = pure ()

trace :: forall e a. CustomUserEvent e => e -> a -> a
trace e a
    | userTracingEnabled && customUserEventEnabled (eventType (undefined :: proxy e)) = do
        let message = BL.toStrict $ runPut $ encodeCustomUserEvent e
        if BS.length message > 2 ^ (16 :: Int)
            then error "eventlog message too long"
            else traceBinaryEvent message a
    | otherwise = a

timeIO :: (MonadIO m, MonadMask m) => ByteString -> m a -> m a
timeIO label
    | userTracingEnabled && customUserEventEnabled Timing =
        bracket_
            (traceIO $ Start label)
            (traceIO $ Stop label)
    | otherwise = id
