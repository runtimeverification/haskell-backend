{-# LANGUAGE FlexibleContexts #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Booster.SMT.Runner (
    SMTContext (..),
    SMT (..),
    SMTEncode (..),
    mkContext,
    closeContext,
    runSMT,
    declare,
    runCmd,
    runCmd_,
    runCheck,
) where

import Control.Monad
import Control.Monad.Extra
import Control.Monad.IO.Class
import Control.Monad.Logger
import Control.Monad.Trans.Reader
import Data.ByteString.Builder qualified as BS
import Data.ByteString.Char8 qualified as BS
import Data.Text (pack)
import SMTLIB.Backends qualified as Backend
import SMTLIB.Backends.Process qualified as Backend
import System.IO (
    BufferMode (..),
    Handle,
    IOMode (..),
    hClose,
    hSetBinaryMode,
    hSetBuffering,
    openFile,
 )

import Booster.SMT.Base
import Booster.SMT.LowLevelCodec

data SMTContext = SMTContext
    { solver :: Backend.Solver
    , solverClose :: IO ()
    , mbTranscript :: Maybe Handle
    }

----------------------------------------
{- TODO (later)
- store prelude of [DeclareCommand] in context (enables hard resets)
- error handling and retries
  - retry counter in context
    - Reader becomes State
- (possibly) run `get-info` on Unknown responses and enhance Unknown constructor
  - smtlib2: reason-unknown = memout | incomplete | SExpr
-}

mkContext ::
    MonadLoggerIO io =>
    Maybe FilePath ->
    io SMTContext
mkContext transcriptPath = do
    logOtherNS "booster" (LevelOther "SMT") "Starting new SMT solver"
    mbTranscript <-
        forM transcriptPath $ \path -> do
            logOtherNS "booster" (LevelOther "SMT") $ "Transcript in file " <> pack path
            liftIO $ do
                h <- openFile path AppendMode
                hSetBuffering h (BlockBuffering Nothing)
                hSetBinaryMode h True
                BS.hPutStrLn h "; starting solver process"
                pure h
    let config = Backend.defaultConfig
    handle <- liftIO $ Backend.new config
    solver <- liftIO $ Backend.initSolver Backend.Queuing $ Backend.toBackend handle
    whenJust mbTranscript $ \h ->
        liftIO $ BS.hPutStrLn h "; solver initialised\n;;;;;;;;;;;;;;;;;;;;;;;"
    logOtherNS "booster" (LevelOther "SMT") "Solver ready to use"
    pure
        SMTContext
            { solver
            , solverClose = Backend.close handle
            , mbTranscript
            }

closeContext :: MonadLoggerIO io => SMTContext -> io ()
closeContext ctxt = do
    logOtherNS "booster" (LevelOther "SMT") "Stopping SMT solver"
    whenJust ctxt.mbTranscript $ \h -> liftIO $ do
        BS.hPutStrLn h "; stopping solver\n;;;;;;;;;;;;;;;;;;;;;;;"
        hClose h
    liftIO $ ctxt.solverClose

newtype SMT m a = SMT (ReaderT SMTContext m a)
    deriving newtype (Functor, Applicative, Monad, MonadIO, MonadLogger, MonadLoggerIO)

runSMT :: SMTContext -> SMT io a -> io a
runSMT ctxt (SMT action) =
    runReaderT action ctxt

declare :: MonadLoggerIO io => [DeclareCommand] -> SMT io ()
declare = mapM_ runCmd

class SMTEncode cmd where
    encode :: cmd -> BS.Builder

    comment :: cmd -> Maybe BS.Builder
    comment _ = Nothing

    -- selecting the actual runner (command_ for Declare and Control, command for query)
    run_ ::
        MonadLoggerIO io =>
        cmd ->
        Backend.Solver ->
        BS.Builder ->
        SMT io BS.ByteString

runCmd_ :: (SMTEncode cmd, MonadLoggerIO io) => cmd -> SMT io ()
runCmd_ = void . runCmd

runCmd :: forall cmd io. (SMTEncode cmd, MonadLoggerIO io) => cmd -> SMT io Response
runCmd cmd = do
    let cmdBS = encode cmd
    ctxt <- SMT ask
    whenJust ctxt.mbTranscript $ \h -> do
        whenJust (comment cmd) $ \c ->
            liftIO (BS.hPutBuilder h c)
        liftIO (BS.hPutBuilder h $ cmdBS <> "\n")
    output <- run_ cmd ctxt.solver cmdBS
    let result = readResponse output
    whenJust ctxt.mbTranscript $
        liftIO . flip BS.hPutStrLn (BS.pack $ "; " <> show output <> ", parsed as " <> show result <> "\n")
    when (isError result) $
        logOtherNS "booster" (LevelOther "SMT") $
            "SMT solver reports: " <> pack (show result)
    pure result
  where
    isError :: Response -> Bool
    isError Error{} = True
    isError _other = False

instance SMTEncode DeclareCommand where
    encode = encodeDeclaration

    comment cmd =
        case getComment cmd of
            "" -> Nothing
            bs ->
                Just
                    . foldl1 (<>)
                    . map (\b -> "; " <> BS.byteString b <> "\n")
                    $ BS.lines bs

    run_ _ s = fmap (const "success") . liftIO . Backend.command_ s

instance SMTEncode QueryCommand where
    encode = encodeQuery

    run_ _ s = fmap BS.toStrict . liftIO . Backend.command s

instance SMTEncode ControlCommand where
    encode Push = "(push)"
    encode Pop = "(pop)"
    encode Exit = "(exit)"

    comment _ = Just ";;;;;;;\n"

    run_ _ s = fmap (const "success") . liftIO . Backend.command_ s

instance SMTEncode SMTCommand where
    encode (Query q) = encode q
    encode (Declare d) = encode d
    encode (Control c) = encode c

    run_ (Query q) = run_ q
    run_ (Declare d) = run_ d
    run_ (Control c) = run_ c

-- typical interaction function for checking satisfiability
runCheck :: MonadLoggerIO io => [DeclareCommand] -> SMT io Response
runCheck decls =
    void (runCmd Push)
        >> mapM_ runCmd decls
        >> runCmd CheckSat
            <* runCmd Pop
