{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Main (main) where

import Booster.LLVM.Internal (LlvmCall (..), LlvmCallArg (..), SomePtr (..))
import Booster.Trace hiding (eventType)
import Booster.Trace.TH
import Control.Exception (catch, throwIO)
import Control.Monad (forM_, unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, execStateT, get, gets, modify')
import Data.Aeson (ToJSON, encode)
import Data.Aeson qualified as Aeson
import Data.Binary.Get
import Data.ByteString (ByteString)
import Data.ByteString.Builder
import Data.ByteString.Lazy qualified as BL
import Data.IntMap (IntMap)
import Data.IntMap qualified as IntMap
import Data.List (intersperse, sortOn)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, isNothing)
import Data.Text (Text)
import Data.Text.Encoding qualified as Text
import FrameDict (FrameDict (..), FrameId, FrameName (FrameName))
import FrameDict qualified
import GHC.Generics (Generic)
import GHC.IO.Handle (BufferMode (BlockBuffering), Handle, hSetBinaryMode, hSetBuffering)
import GHC.IO.Handle.FD (withBinaryFile)
import GHC.IO.IOMode (IOMode (AppendMode))
import GHC.RTS.Events qualified as Events
import GHC.Stack (HasCallStack)
import Options.Applicative qualified as Options
import System.Directory (removeFile)
import System.FilePath ((<.>))
import System.IO.Error (isDoesNotExistError)

type CustomUserEvents = '[Start, Stop, LlvmCall]

$(mkSumPatterns @CustomUserEvents)

type CustomUserEventData =
    (Events.Timestamp, Either Events.EventInfo (Sum CustomUserEvents), Maybe Int)

parseEventLog :: Events.Event -> CustomUserEventData
parseEventLog Events.Event{evTime, evSpec, evCap} =
    ( evTime
    , case evSpec of
        Events.UserBinaryMessage msg -> case runGet (decodeCustomUserEvent @CustomUserEvents) $ BL.fromStrict msg of
            Unmatched -> Left evSpec
            userEvent -> Right userEvent
        _ -> Left evSpec
    , evCap
    )

readLog :: FilePath -> IO [CustomUserEventData]
readLog file =
    Events.readEventLogFromFile file
        >>= either error (pure . map parseEventLog . sortOn Events.evTime . Events.events . Events.dat)

data FrameEventType = Open | Close
    deriving (Eq, Ord, Show)

instance ToJSON FrameEventType where
    toJSON Open = Aeson.String "O"
    toJSON Close = Aeson.String "C"

data FrameEvent = FrameEvent
    { eventType :: !FrameEventType
    , eventAt :: !Events.Timestamp
    , eventFrameId :: !FrameId
    }
    deriving (Eq, Ord, Show)
    deriving (Generic)

instance ToJSON FrameEvent where
    toJSON FrameEvent{eventType, eventAt, eventFrameId} =
        Aeson.object
            [ "type" Aeson..= eventType
            , "at" Aeson..= eventAt
            , "frame" Aeson..= eventFrameId
            ]

data ProcessAnalysis = ProcessAnalysis
    { frames :: !FrameDict
    , caps :: !(IntMap Events.ThreadId)
    , endTime :: !Events.Timestamp
    , frameBuilders :: !(Map Events.ThreadId Builder)
    , stacks :: !(Map Events.ThreadId [FrameEvent])
    }
    deriving (Generic)

emptyProcessAnalysis :: ProcessAnalysis
emptyProcessAnalysis =
    ProcessAnalysis
        { frames = FrameDict.empty
        , caps = IntMap.empty
        , endTime = 0
        , frameBuilders = mempty
        , stacks = mempty
        }

expectThreadId ::
    HasCallStack =>
    Int ->
    StateT ProcessAnalysis IO Events.ThreadId
expectThreadId cap =
    gets (IntMap.lookup cap . caps) >>= \case
        Just threadId -> pure threadId
        Nothing -> error "expected thread"

pushAndExtractTail ::
    Events.ThreadId -> FrameEvent -> StateT ProcessAnalysis IO [FrameEvent]
pushAndExtractTail threadId frame = do
    -- inspect stack before pushing to extract tail of
    -- current stack
    ss <- gets stacks
    let s = fromMaybe [] $ Map.lookup threadId ss
    modify' $ \st@ProcessAnalysis{stacks} -> st{stacks = Map.insert threadId (frame : s) stacks}
    pure s

popAndExtractTail :: Events.ThreadId -> FrameId -> StateT ProcessAnalysis IO [FrameEvent]
popAndExtractTail threadId frameId = do
    ProcessAnalysis{stacks, frames} <- get
    let s = fromMaybe [] $ Map.lookup threadId stacks
    case s of
        [] -> do
            let mFrameName = FrameDict.lookup frameId frames
                frameName = maybe (show frameId) show mFrameName
            (error . unwords)
                [ "expected"
                , frameName
                , "but found nothing"
                ]
        (FrameEvent{eventFrameId} : stack')
            | eventFrameId == frameId ->
                modify' $ \st -> st{stacks = Map.insert threadId stack' stacks}
            | otherwise -> do
                let mFrameName = FrameDict.lookup frameId frames
                    mFrameName' = FrameDict.lookup eventFrameId frames
                let frameName = maybe (show frameId) show mFrameName
                    frameName' = maybe (show eventFrameId) show mFrameName'
                (error . unwords)
                    [ "expected"
                    , frameName
                    , "but found"
                    , frameName'
                    ]
    pure s

-- | FrameFilter can be used to filter out certain user events, based on matching as substring of the event label.
applyFrameFilter :: FrameDict.FrameFilter -> [FrameEvent] -> FrameId -> Bool
applyFrameFilter frameFilter stack frameId =
    (null matchingIds || frameId `elem` matchingIds)
        && frameId `notElem` notMatchingIds
        && all ((`notElem` notMatchingChildrenIds) . eventFrameId) stack
  where
    FrameDict.FrameFilter{matchingIds, notMatchingIds, notMatchingChildrenIds} = frameFilter

emitFrameEvent :: Events.ThreadId -> FrameEvent -> StateT ProcessAnalysis IO ()
emitFrameEvent threadId frame = do
    builders <- gets frameBuilders
    let builder = case Map.lookup threadId builders of
            Nothing -> charUtf8 '[' <> lazyByteString (encode frame)
            Just b -> b <> charUtf8 '\n' <> charUtf8 ',' <> lazyByteString (encode frame)
    modify' $ \st -> st{frameBuilders = Map.insert threadId builder builders}

emitSpeedscopeProfile ::
    FilePath -> FrameDict -> [(Events.ThreadId, Builder)] -> Events.Timestamp -> IO ()
emitSpeedscopeProfile file frames threads endTime = do
    removeFileIfExists file
    withBinaryFile file AppendMode $ \jsonHandle -> do
        hSetBinaryMode jsonHandle True
        hSetBuffering jsonHandle $ BlockBuffering Nothing
        let schema = lazyByteString "{\"$schema\":\"https://www.speedscope.app/file-format-schema.json\","
            shared =
                lazyByteString "\"shared\":{\"frames\":["
                    <> mconcat (intersperse (charUtf8 ',') [lazyByteString $ encode f | f <- FrameDict.toList frames])
                    <> lazyByteString "]},"
            profiles = lazyByteString "\"profiles\":["
        hPutBuilder jsonHandle $ schema <> shared <> profiles
        forM_ (intersperse Nothing $ map Just threads) $ \case
            Nothing -> hPutBuilder jsonHandle $ charUtf8 ','
            Just (threadId, events) -> do
                let meta =
                        lazyByteString "{\"type\":\"evented\",\"name\":\"thread "
                            <> (stringUtf8 $ show threadId)
                            <> lazyByteString "\","
                            <> lazyByteString "\"unit\":\"nanoseconds\",\"startValue\":0,\"endValue\":"
                            <> (stringUtf8 $ show endTime)
                            <> charUtf8 ','
                            <> lazyByteString "\"events\":"
                hPutBuilder jsonHandle meta
                hPutBuilder jsonHandle $ events <> lazyByteString "]}"
        hPutBuilder jsonHandle $ lazyByteString "]}"

emitLlvmCall ::
    Handle -> Maybe (ByteString, SomePtr) -> ByteString -> [LlvmCallArg] -> IO ()
emitLlvmCall llvmCallsHandle ret call args = do
    let prettyRet = case ret of
            Just (ty, SomePtr ptr) -> byteString ty <> lazyByteString " v" <> byteString ptr <> lazyByteString " = "
            _ -> ""

        prettyArgs =
            charUtf8 '('
                <> mconcat
                    ( intersperse (charUtf8 ',') $
                        map
                            ( \case
                                LlvmCallArgByteString str -> charUtf8 '"' <> byteString str <> charUtf8 '"'
                                LlvmCallArgWord int -> word64Dec (fromIntegral int)
                                LlvmCallArgPtr (SomePtr ptr) -> charUtf8 'v' <> byteString ptr
                            )
                            args
                    )
                <> charUtf8 ')'
    hPutBuilder llvmCallsHandle $ prettyRet <> byteString call <> prettyArgs <> lazyByteString ";\n"

analyse ::
    [Text] -> [Text] -> [Text] -> Handle -> CustomUserEventData -> StateT ProcessAnalysis IO ()
analyse matching nonMatching notMatchingChildren llvmCallsHandle (evTime, evSpec, evCap) = do
    modify' $ \s@ProcessAnalysis{endTime} -> s{endTime = max endTime evTime}
    case evSpec of
        -- RunThread/StopThread events are used to record which thread is currently executing
        -- This may be useful in the future if the backend becomes multi-threaded
        Left Events.RunThread{Events.thread = threadId} -> do
            cap <- maybe (error "expected capability") pure evCap
            modify' $ \s@ProcessAnalysis{caps} -> s{caps = IntMap.insert cap threadId caps}
        Left Events.StopThread{} -> do
            cap <- maybe (error "expected capability") pure evCap
            modify' $ \s@ProcessAnalysis{caps} -> s{caps = IntMap.delete cap caps}
        Right (StartE (Start ident)) -> do
            cap <- maybe (error "expected capability") pure evCap
            eventThreadId <- expectThreadId cap
            frameDict <- gets frames
            let (eventFrameId, frameDict') =
                    FrameDict.insert
                        (FrameName $ Text.decodeUtf8 ident)
                        matching
                        nonMatching
                        notMatchingChildren
                        frameDict
                frameFilter = FrameDict.frameFilter $ fromMaybe frameDict frameDict'

                frame =
                    FrameEvent
                        { eventType = Open
                        , eventAt = evTime
                        , eventFrameId
                        }

            -- if frameDict was updated, store the updated version
            maybe (pure ()) (\d -> modify' $ \st -> st{frames = d}) frameDict'

            -- add the opening event to the stack of all events for the current thread
            stack <- pushAndExtractTail eventThreadId frame
            -- if we aren't filtering an event, emit it to the json builder
            when (applyFrameFilter frameFilter stack eventFrameId) $
                emitFrameEvent eventThreadId frame
        Right (StopE (Stop ident)) -> do
            cap <- maybe (error "expected capability") pure evCap
            eventThreadId <- expectThreadId cap
            frameDict <- gets frames
            let (eventFrameId, frameDict') =
                    FrameDict.insert
                        (FrameName $ Text.decodeUtf8 ident)
                        matching
                        nonMatching
                        notMatchingChildren
                        frameDict
                frameFilter = FrameDict.frameFilter frameDict

            unless (isNothing frameDict') $ error "expected no new inserts in the FrameDict"

            let frame =
                    FrameEvent
                        { eventType = Close
                        , eventAt = evTime
                        , eventFrameId
                        }

            -- popAndExtractTail checks that the closing event matches the top-most
            -- open event.
            stack <- popAndExtractTail eventThreadId eventFrameId
            when (applyFrameFilter frameFilter stack eventFrameId) $
                emitFrameEvent eventThreadId frame
        Right (LlvmCallE LlvmCall{ret, call, args}) -> lift $ emitLlvmCall llvmCallsHandle ret call args
        _ -> pure ()

removeFileIfExists :: FilePath -> IO ()
removeFileIfExists fileName = removeFile fileName `catch` handleExists
  where
    handleExists e
        | isDoesNotExistError e = return ()
        | otherwise = throwIO e

data Options = Options
    { filename :: !FilePath
    , matching :: ![Text]
    , notMatching :: ![Text]
    , notMatchingChildren :: ![Text]
    }

parseOptions :: Options.Parser Options
parseOptions =
    Options
        <$> Options.strArgument
            ( mconcat
                [ Options.metavar "FILENAME"
                , Options.help "eventlog file"
                ]
            )
        <*> (Options.many . Options.strOption)
            ( mconcat
                [ Options.metavar "STRING"
                , Options.long "matching"
                , Options.help
                    "only emit events where STRING occurs as a substring of the name"
                ]
            )
        <*> (Options.many . Options.strOption)
            ( mconcat
                [ Options.metavar "STRING"
                , Options.long "not-matching"
                , Options.help
                    "only emit events where STRING does not occur\
                    \ as a substring of the name"
                ]
            )
        <*> (Options.many . Options.strOption)
            ( mconcat
                [ Options.metavar "STRING"
                , Options.long "not-matching-children"
                , Options.help
                    "only emit children of events where STRING\
                    \ does not occur as a substring of the name"
                ]
            )

main :: IO ()
main = do
    Options{filename, matching, notMatching, notMatchingChildren} <- Options.execParser inf

    eventLogData <- readLog filename
    removeFileIfExists "llvm-calls.c"
    ProcessAnalysis{frames, frameBuilders, endTime} <- withBinaryFile "llvm-calls.c" AppendMode $ \handle -> do
        hSetBinaryMode handle True
        hSetBuffering handle $ BlockBuffering Nothing

        flip execStateT emptyProcessAnalysis $ do
            forM_ eventLogData $
                analyse matching notMatching notMatchingChildren handle

            eventAt <- gets endTime
            stacks <- gets stacks
            frameFilter <- FrameDict.frameFilter <$> gets frames

            -- this should not happen, but somehow the evenlog may end up containing open events
            -- without a corresponding close. The code below simply emits close events at `endTime` for
            -- any remaining events on all the stacks.
            forM_ (Map.toList stacks) $ \(eventThreadId, frames) ->
                forM_ frames $ \frame@FrameEvent{eventFrameId} -> do
                    stack <- popAndExtractTail eventThreadId eventFrameId
                    when (applyFrameFilter frameFilter stack eventFrameId) $
                        emitFrameEvent eventThreadId frame{eventAt, eventType = Close}

    when (Map.size frameBuilders > 0) $ do
        removeFileIfExists $ filename <.> "json"
        emitSpeedscopeProfile (filename <.> "json") frames (Map.toList frameBuilders) endTime
  where
    inf =
        Options.info
            parseOptions
            ( mconcat
                [ Options.fullDesc
                , Options.progDesc "Write a speedscope profile and LLVM Calls for FILENAME"
                , Options.header "eventlog-parser"
                ]
            )
