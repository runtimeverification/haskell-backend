{-# LANGUAGE CApiFFI #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : Kore.Builtin.IO
Description : Built-in I/O (limited support)
Copyright   : (c) Runtime Verification, 2018-2022
License     : BSD-3-Clause
Maintainer  : dwight.guth@runtimeverification.com

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.IO as IO
@
-}
module Kore.Builtin.IO (
    builtinFunctions,
    verifiers,
    logStringKey,
) where

import Data.Bits ((.|.))
import Data.ByteString.Internal (createUptoN')
import Data.ByteString.Unsafe (unsafeUseAsCStringLen)
import Data.HashMap.Strict qualified as HashMap
import Data.String (
    IsString,
 )
import Data.Text (
    Text,
    unpack,
 )
import Data.Text.Encoding (decodeUtf8, encodeUtf8)
import Foreign.C.Error
import Foreign.C.String (CString)
import Foreign.C.Types (CChar, CInt (..), CSize (..))
import Foreign.ForeignPtr (mallocForeignPtr, withForeignPtr)
import Foreign.Ptr (Ptr, castPtr)
import Foreign.Storable (peek, sizeOf)
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.String qualified as String
import Kore.IndexedModule.MetadataTools qualified as Tools (
    symbolAttributes,
 )
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (..),
 )

import Kore.Attribute.Symbol (Injective (..), SortInjection (..), Symbol (injective, sortInjection), defaultSymbolAttributes)
import Kore.Attribute.Synthetic (
    synthesize,
 )
import Kore.Builtin.Int qualified as Int
import Kore.Internal.InternalInt (
    InternalInt (..),
 )
import Kore.Internal.InternalString (
    InternalString (..),
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Symbol (
    Symbol (..),
 )
import Kore.Internal.TermLike (
    pattern InternalInt_,
    pattern InternalString_,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Log.InfoUserLog
import Kore.Simplify.Simplify (
    BuiltinAndAxiomSimplifier,
    MonadSimplify,
    askMetadataTools,
 )
import Kore.Syntax.Id (
    implicitId,
 )
import Prelude.Kore
import System.Posix.IO
import System.Posix.Internals (
    o_APPEND,
    o_CREAT,
    o_EXCL,
    o_NOCTTY,
    o_NONBLOCK,
    o_RDONLY,
    o_RDWR,
    o_TRUNC,
    o_WRONLY,
    withFilePath,
 )
import System.Posix.Types

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers = mempty
        , symbolVerifiers
        , patternVerifierHook = mempty
        }

symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
        [
            ( logStringKey
            , Builtin.verifySymbol Builtin.acceptAnySort [String.assertSort]
            )
        ]

builtinFunctions :: Text -> Maybe BuiltinAndAxiomSimplifier
builtinFunctions key
    | key == logStringKey = Just $ Builtin.functionEvaluator evalLogString
    | key == openKey = Just $ Builtin.functionEvaluator evalOpen
    | key == getcKey = Just $ Builtin.functionEvaluator evalGetc
    | key == readKey = Just $ Builtin.functionEvaluator evalRead
    | key == closeKey = Just $ Builtin.functionEvaluator evalClose
    | key == writeKey = Just $ Builtin.functionEvaluator evalWrite
    | otherwise = Nothing

mkDotk ::
    MonadSimplify m =>
    TermLike.InternalVariable variable =>
    TermLike.Sort ->
    m (Pattern.Pattern variable)
mkDotk sort = do
    tools <- askMetadataTools
    let ident = implicitId "dotk"
    return $
        Pattern.fromTermLike $
            TermLike.mkApplySymbol
                Symbol
                    { symbolConstructor = ident
                    , symbolParams = []
                    , symbolSorts =
                        ApplicationSorts
                            { applicationSortsOperands = []
                            , applicationSortsResult = sort
                            }
                    , symbolAttributes = Tools.symbolAttributes tools ident
                    }
                []

evalLogString :: Builtin.Function
evalLogString _ _ [] = Builtin.wrongArity logStringKey
evalLogString _ sort [InternalString_ InternalString{internalStringValue}] = do
    infoUserLog internalStringValue
    mkDotk sort
evalLogString _ _ [_] = empty
evalLogString _ _ (_ : _ : _) = Builtin.wrongArity logStringKey

logStringKey :: IsString s => s
logStringKey = "IO.logString"

returnErrnoIfMinus1OrRetry :: (Eq a, Num a) => IO a -> IO (Either Errno a)
returnErrnoIfMinus1OrRetry f =
    do
        res <- f
        if res == -1
            then do
                err <- getErrno
                if err == eINTR
                    then returnErrnoIfMinus1OrRetry f
                    else return $ Left err
            else return $ Right res

parseMode :: Text -> Maybe (OpenMode, OpenFileFlags, Maybe FileMode)
parseMode = \case
    "r" -> Just (ReadOnly, defaultFileFlags, Nothing)
    "r+" -> Just (ReadWrite, defaultFileFlags, Nothing)
    "w" -> Just (WriteOnly, defaultFileFlags{trunc = True}, Just 0o666)
    "w+" -> Just (ReadWrite, defaultFileFlags{trunc = True}, Just 0o666)
    "a" -> Just (WriteOnly, defaultFileFlags{append = True}, Just 0o666)
    "a+" -> Just (ReadWrite, defaultFileFlags{append = True}, Just 0o666)
    _ -> Nothing

-- copied from System.Posix.IO.Common as this module is hidden
open_ ::
    -- | Pathname to open
    CString ->
    -- | Read-only, read-write or write-only
    OpenMode ->
    -- |Just x => creates the file with the given modes, Nothing => the file must exist.
    Maybe FileMode ->
    -- | Append, exclusive, etc.
    OpenFileFlags ->
    IO Fd
open_ str how maybe_mode OpenFileFlags{..} =
    Fd <$> c_open str all_flags mode_w
  where
    all_flags = creat .|. flags .|. open_mode

    (creat, mode_w) = case maybe_mode of
        Nothing -> (0, 0)
        Just x -> (o_CREAT, x)

    flags =
        (if append then o_APPEND else 0)
            .|. (if exclusive then o_EXCL else 0)
            .|. (if noctty then o_NOCTTY else 0)
            .|. (if nonBlock then o_NONBLOCK else 0)
            .|. (if trunc then o_TRUNC else 0)

    open_mode = case how of
        ReadOnly -> o_RDONLY
        WriteOnly -> o_WRONLY
        ReadWrite -> o_RDWR

foreign import capi unsafe "HsUnix.h open"
    c_open :: CString -> CInt -> CMode -> IO CInt

openRaw ::
    -- | Pathname to open
    FilePath ->
    -- | Read-only, read-write or write-only
    OpenMode ->
    -- |Just x => creates the file with the given modes, Nothing => the file must exist.
    Maybe FileMode ->
    -- | Append, exclusive, truncate, etc.
    OpenFileFlags ->
    IO (Either Errno Fd)
openRaw filepath how maybe_mode flags =
    withFilePath filepath $ \str ->
        returnErrnoIfMinus1OrRetry $
            open_ str how maybe_mode flags

ioErrorSort, intSort, stringSort :: TermLike.Sort
ioErrorSort = TermLike.SortActualSort $ TermLike.SortActual (implicitId "SortIOError") []
intSort = TermLike.SortActualSort $ TermLike.SortActual (implicitId "SortInt") []
stringSort = TermLike.SortActualSort $ TermLike.SortActual (implicitId "SortString") []

mkSortInjection ::
    TermLike.InternalVariable variable =>
    TermLike.Sort ->
    TermLike.TermLike variable ->
    TermLike.TermLike variable
mkSortInjection injTo termLike =
    (synthesize . TermLike.InjF)
        TermLike.Inj
            { injConstructor = implicitId "inj"
            , injFrom
            , injTo
            , injChild = termLike
            , injAttributes
            }
  where
    injFrom = TermLike.termLikeSort termLike
    injAttributes =
        defaultSymbolAttributes
            { injective = Injective True
            , sortInjection = SortInjection True
            }

errnoToEitherTextInt :: Errno -> Either Text CInt
errnoToEitherTextInt errno@(Errno cint)
    -- EOF handled separately in getcRaw
    | errno == e2BIG = Left "E2BIG"
    | errno == eACCES = Left "EACCES"
    | errno == eAGAIN = Left "EAGAIN"
    | errno == eBADF = Left "EBADF"
    | errno == eBUSY = Left "EBUSY"
    | errno == eCHILD = Left "ECHILD"
    | errno == eDEADLK = Left "EDEADLK"
    | errno == eDOM = Left "EDOM"
    | errno == eEXIST = Left "EEXIST"
    | errno == eFAULT = Left "EFAULT"
    | errno == eFBIG = Left "EFBIG"
    | errno == eINTR = Left "EINTR"
    | errno == eINVAL = Left "EINVAL"
    | errno == eIO = Left "EIO"
    | errno == eISDIR = Left "EISDIR"
    | errno == eMFILE = Left "EMFILE"
    | errno == eMLINK = Left "EMLINK"
    | errno == eNAMETOOLONG = Left "ENAMETOOLONG"
    | errno == eNFILE = Left "ENFILE"
    | errno == eNODEV = Left "ENODEV"
    | errno == eNOENT = Left "ENOENT"
    | errno == eNOEXEC = Left "ENOEXEC"
    | errno == eNOLCK = Left "ENOLCK"
    | errno == eNOMEM = Left "ENOMEM"
    | errno == eNOSPC = Left "ENOSPC"
    | errno == eNOSYS = Left "ENOSYS"
    | errno == eNOTDIR = Left "ENOTDIR"
    | errno == eNOTEMPTY = Left "ENOTEMPTY"
    | errno == eNOTTY = Left "ENOTTY"
    | errno == eNXIO = Left "ENXIO"
    | errno == ePERM = Left "EPERM"
    | errno == ePIPE = Left "EPIPE"
    | errno == eRANGE = Left "ERANGE"
    | errno == eROFS = Left "EROFS"
    | errno == eSPIPE = Left "ESPIPE"
    | errno == eSRCH = Left "ESRCH"
    | errno == eXDEV = Left "EXDEV"
    | errno == eWOULDBLOCK = Left "EWOULDBLOCK"
    | errno == eINPROGRESS = Left "EINPROGRESS"
    | errno == eALREADY = Left "EALREADY"
    | errno == eNOTSOCK = Left "ENOTSOCK"
    | errno == eDESTADDRREQ = Left "EDESTADDRREQ"
    | errno == eMSGSIZE = Left "EMSGSIZE"
    | errno == ePROTOTYPE = Left "EPROTOTYPE"
    | errno == eNOPROTOOPT = Left "ENOPROTOOPT"
    | errno == ePROTONOSUPPORT = Left "EPROTONOSUPPORT"
    | errno == eSOCKTNOSUPPORT = Left "ESOCKTNOSUPPORT"
    | errno == eOPNOTSUPP = Left "EOPNOTSUPP"
    | errno == ePFNOSUPPORT = Left "EPFNOSUPPORT"
    | errno == eAFNOSUPPORT = Left "EAFNOSUPPORT"
    | errno == eADDRINUSE = Left "EADDRINUSE"
    | errno == eADDRNOTAVAIL = Left "EADDRNOTAVAIL"
    | errno == eNETDOWN = Left "ENETDOWN"
    | errno == eNETUNREACH = Left "ENETUNREACH"
    | errno == eNETRESET = Left "ENETRESET"
    | errno == eCONNABORTED = Left "ECONNABORTED"
    | errno == eCONNRESET = Left "ECONNRESET"
    | errno == eNOBUFS = Left "ENOBUFS"
    | errno == eISCONN = Left "EISCONN"
    | errno == eNOTCONN = Left "ENOTCONN"
    | errno == eSHUTDOWN = Left "ESHUTDOWN"
    | errno == eTOOMANYREFS = Left "ETOOMANYREFS"
    | errno == eTIMEDOUT = Left "ETIMEDOUT"
    | errno == eCONNREFUSED = Left "ECONNREFUSED"
    | errno == eHOSTDOWN = Left "EHOSTDOWN"
    | errno == eHOSTUNREACH = Left "EHOSTUNREACH"
    | errno == eLOOP = Left "ELOOP"
    -- "EOVERFLOW" not defined
    | otherwise = Right cint

mkIOErrorFromErrno ::
    MonadSimplify m =>
    TermLike.InternalVariable variable =>
    TermLike.Sort ->
    Errno ->
    m (Pattern.Pattern variable)
mkIOErrorFromErrno sort err = mkIOError sort $ errnoToEitherTextInt err

mkIOError ::
    MonadSimplify m =>
    TermLike.InternalVariable variable =>
    TermLike.Sort ->
    Either Text CInt ->
    m (Pattern.Pattern variable)
mkIOError sort err = do
    tools <- askMetadataTools
    let ioErrorKnown str =
            let ident = implicitId $ "Lbl'Hash'" <> str
             in Symbol
                    { symbolConstructor = ident
                    , symbolParams = []
                    , symbolSorts =
                        ApplicationSorts
                            { applicationSortsOperands = []
                            , applicationSortsResult = ioErrorSort
                            }
                    , symbolAttributes = Tools.symbolAttributes tools ident
                    }
        ioErrorUnknown =
            let ident = implicitId "Lbl'Hash'unknownIOError"
             in Symbol
                    { symbolConstructor = ident
                    , symbolParams = []
                    , symbolSorts =
                        ApplicationSorts
                            { applicationSortsOperands = [intSort]
                            , applicationSortsResult = ioErrorSort
                            }
                    , symbolAttributes = Tools.symbolAttributes tools ident
                    }
    return $
        Pattern.fromTermLike $
            mkSortInjection sort $ case err of
                Left str -> TermLike.mkApplySymbol (ioErrorKnown str) []
                Right cint -> TermLike.mkApplySymbol ioErrorUnknown [Int.asInternal intSort $ toInteger cint]

evalOpen :: Builtin.Function
evalOpen _ sort [InternalString_ InternalString{internalStringValue = path}, InternalString_ InternalString{internalStringValue = mode_str}]
    | Just (mode, flags, mFilemode) <- parseMode mode_str = do
        res <- liftIO $ openRaw (unpack path) mode mFilemode flags
        case res of
            Left err -> do
                mkIOErrorFromErrno sort err
            Right fd ->
                toInteger fd
                    & Int.asInternal intSort
                    & mkSortInjection sort
                    & Pattern.fromTermLike
                    & return
evalOpen _ _ [_, _] = empty
evalOpen _ _ _ = Builtin.wrongArity openKey

openKey :: IsString s => s
openKey = "IO.open"

foreign import ccall safe "read"
    c_safe_read :: CInt -> Ptr CChar -> CSize -> IO CSsize

getcRaw ::
    Fd ->
    IO (Either (Either Text CInt) Integer)
getcRaw fd = do
    cF <- mallocForeignPtr
    withForeignPtr cF $ \(c :: Ptr CChar) -> do
        rc <-
            returnErrnoIfMinus1OrRetry $
                c_safe_read (fromIntegral fd) c (fromIntegral $ sizeOf (undefined :: CChar))
        case rc of
            Left err -> return $ Left $ errnoToEitherTextInt err
            Right 0 -> return $ Left $ Left "EOF"
            Right _ -> (Right . toInteger) <$> peek c

evalGetc :: Builtin.Function
evalGetc _ sort [InternalInt_ InternalInt{internalIntValue = fd}] = do
    res <- liftIO $ getcRaw (fromInteger fd)
    case res of
        Left err -> mkIOError sort err
        Right c ->
            Int.asInternal intSort c
                & mkSortInjection sort
                & Pattern.fromTermLike
                & return
evalGetc _ _ [_] = empty
evalGetc _ _ _ = Builtin.wrongArity openKey

getcKey :: IsString s => s
getcKey = "IO.getc"

readRaw ::
    Fd ->
    -- |How many bytes to read
    ByteCount ->
    -- |The bytes read
    IO (Either Errno Text)
readRaw fd nbytes = do
    (str, mErr) <- createUptoN' (fromIntegral nbytes) $ \buf -> do
        rc <-
            returnErrnoIfMinus1OrRetry $
                c_safe_read (fromIntegral fd) (castPtr buf) nbytes
        case rc of
            Left err -> return (0, Just err)
            Right 0 -> return (0, Nothing)
            Right n -> return (fromIntegral n, Nothing)
    return $ case mErr of
        Just err -> Left err
        Nothing -> Right $ decodeUtf8 str

evalRead :: Builtin.Function
evalRead _ sort [InternalInt_ InternalInt{internalIntValue = fd}, InternalInt_ InternalInt{internalIntValue = len}] = do
    res <- liftIO $ readRaw (fromInteger fd) (fromInteger len)
    case res of
        Left err -> mkIOErrorFromErrno sort err
        Right txt ->
            txt
                & String.asInternal stringSort
                & mkSortInjection sort
                & Pattern.fromTermLike
                & return
evalRead _ _ [_, _] = empty
evalRead _ _ _ = Builtin.wrongArity openKey

readKey :: IsString s => s
readKey = "IO.read"

returnErrnoIfMinus1 :: (Eq a, Num a) => IO a -> IO (Either Errno a)
returnErrnoIfMinus1 f =
    do
        res <- f
        if res == -1
            then do
                err <- getErrno
                return $ Left err
            else return $ Right res

closeRaw :: Fd -> IO (Maybe Errno)
closeRaw (Fd fd) = do
    -- Here we don't to retry on EINTR because according to
    --  http://pubs.opengroup.org/onlinepubs/9699919799/functions/close.html
    -- "with errno set to [EINTR] [...] the state of fildes is unspecified"
    -- and on Linux, already the first close() removes the FD from the process's
    -- FD table so closing a second time is invalid
    -- (see http://man7.org/linux/man-pages/man2/close.2.html#NOTES).
    rc <- returnErrnoIfMinus1 $ c_close fd
    return $ case rc of
        Left err -> Just err
        Right _ -> Nothing

foreign import ccall unsafe "HsUnix.h close"
    c_close :: CInt -> IO CInt

evalClose :: Builtin.Function
evalClose _ sort [InternalInt_ InternalInt{internalIntValue = fd}] = do
    res <- liftIO $ closeRaw (fromInteger fd)
    case res of
        Just err -> mkIOErrorFromErrno sort err
        Nothing -> mkDotk sort
evalClose _ _ [_] = empty
evalClose _ _ _ = Builtin.wrongArity openKey

closeKey :: IsString s => s
closeKey = "IO.close"

writeRaw :: Fd -> Text -> IO (Maybe Errno)
writeRaw fd str =
    unsafeUseAsCStringLen (encodeUtf8 str) $ \(buf, len) ->
        either Just (const Nothing)
            <$> returnErrnoIfMinus1OrRetry
                (c_safe_write (fromIntegral fd) (castPtr buf) (fromIntegral len))

foreign import ccall safe "write"
    c_safe_write :: CInt -> Ptr CChar -> CSize -> IO CSsize

evalWrite :: Builtin.Function
evalWrite _ sort [InternalInt_ InternalInt{internalIntValue = fd}, InternalString_ InternalString{internalStringValue = str}] = do
    res <- liftIO $ writeRaw (fromInteger fd) str
    case res of
        Just err -> mkIOErrorFromErrno sort err
        Nothing -> mkDotk sort
evalWrite _ _ [_, _] = empty
evalWrite _ _ _ = Builtin.wrongArity openKey

writeKey :: IsString s => s
writeKey = "IO.write"
