{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Booster.LLVM.Internal (
    API (..),
    KorePatternAPI (..),
    runLLVM,
    withDLib,
    mkAPI,
    ask,
    marshallTerm,
    marshallSort,
    -- testing only
    KoreStringPatternAPI (..),
    KoreSymbolAPI (..),
    KoreSortAPI (..),
    SomePtr (..),
    somePtr,
    LlvmCall (..),
    LlvmCallArg (..),
    LlvmVar (..),
) where

import Booster.LLVM.TH (dynamicBindings)
import Booster.Pattern.Base
import Booster.Pattern.Binary hiding (Block)
import Booster.Pattern.Util (sortOfTerm)
import Booster.Prettyprinter qualified as KPretty
import Booster.Trace
import Booster.Trace qualified as Trace
import Control.Monad (foldM, forM_, void, (>=>))
import Control.Monad.Catch (MonadCatch, MonadMask, MonadThrow)
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Control.Monad.Trans.Reader qualified as Reader
import Data.Binary (Binary, get, put)
import Data.ByteString.Builder
import Data.ByteString.Char8 (ByteString, pack)
import Data.ByteString.Char8 qualified as BS
import Data.ByteString.Lazy qualified as BL
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.List qualified as List (intersperse)
import Foreign (ForeignPtr, finalizeForeignPtr, newForeignPtr, withForeignPtr)
import Foreign qualified
import Foreign.C qualified as C
import Foreign.C.Types (CSize (..))
import Foreign.Marshal (alloca)
import Foreign.Storable (peek)
import GHC.Generics (Generic)
import Prettyprinter (Pretty (..))
import System.Posix.DynamicLinker qualified as Linker

data KorePattern
data KoreSort
data KoreSymbol
data Block
type SizeT = CSize

type KorePatternPtr = ForeignPtr KorePattern
type KoreSymbolPtr = ForeignPtr KoreSymbol
type KoreSortPtr = ForeignPtr KoreSort

$(dynamicBindings "./cbits/kllvm-c.h")

newtype KoreStringPatternAPI = KoreStringPatternAPI
    { new :: ByteString -> IO KorePatternPtr
    }

newtype KoreTokenPatternAPI = KoreTokenPatternAPI
    { new :: ByteString -> KoreSortPtr -> IO KorePatternPtr
    }

data KoreSymbolAPI = KoreSymbolAPI
    { new :: ByteString -> IO KoreSymbolPtr
    , addArgument :: KoreSymbolPtr -> KoreSortPtr -> IO KoreSymbolPtr
    , cache :: IORef (HashMap (Symbol, [Sort]) KoreSymbolPtr)
    }

data KoreSortAPI = KoreSortAPI
    { new :: ByteString -> IO KoreSortPtr
    , addArgument :: KoreSortPtr -> KoreSortPtr -> IO KoreSortPtr
    , dump :: KoreSortPtr -> IO String
    , cache :: IORef (HashMap Sort KoreSortPtr)
    }

data KorePatternAPI = KorePatternAPI
    { new :: ByteString -> IO KorePatternPtr
    , addArgument :: KorePatternPtr -> KorePatternPtr -> IO KorePatternPtr
    , fromSymbol :: KoreSymbolPtr -> IO KorePatternPtr
    , string :: KoreStringPatternAPI
    , token :: KoreTokenPatternAPI
    , dump :: KorePatternPtr -> IO String
    }

data API = API
    { patt :: KorePatternAPI
    , symbol :: KoreSymbolAPI
    , sort :: KoreSortAPI
    , simplifyBool :: KorePatternPtr -> IO Bool
    , simplify :: KorePatternPtr -> KoreSortPtr -> IO ByteString
    }

newtype LLVM a = LLVM (ReaderT API IO a)
    deriving newtype (Functor, Applicative, Monad, MonadIO, MonadThrow, MonadCatch, MonadMask)

newtype SomePtr = SomePtr ByteString
    deriving newtype (Binary)

somePtr :: Show a => a -> SomePtr
somePtr ptr = SomePtr $ pack $ show ptr

data LlvmCallArg
    = LlvmCallArgByteString ByteString
    | LlvmCallArgWord Word
    | LlvmCallArgPtr SomePtr
    deriving (Generic)

instance Binary LlvmCallArg

data LlvmCall = LlvmCall
    { ret :: Maybe (ByteString, SomePtr)
    , call :: ByteString
    , args :: [LlvmCallArg]
    }
instance CustomUserEvent LlvmCall where
    encodeUserEvent (LlvmCall{ret, call, args}) = put ret <> put call <> put args
    decodeUserEvent = LlvmCall <$> get <*> get <*> get
    userEventTag _ = "LLVM "
    eventType _ = LlvmCalls

    prettyPrintUserEvent (LlvmCall{ret, call, args}) =
        let prettyRet = case ret of
                Just (ty, SomePtr ptr) -> byteString ty <> lazyByteString " v" <> byteString ptr <> lazyByteString " = "
                _ -> ""

            prettyArgs =
                charUtf8 '('
                    <> mconcat
                        ( List.intersperse (charUtf8 ',') $
                            map
                                ( \case
                                    LlvmCallArgByteString str -> charUtf8 '"' <> byteString str <> charUtf8 '"'
                                    LlvmCallArgWord int -> word64Dec (fromIntegral int)
                                    LlvmCallArgPtr (SomePtr ptr) -> charUtf8 'v' <> byteString ptr
                                )
                                args
                        )
                    <> charUtf8 ')'
            call_str = prettyRet <> byteString "api." <> byteString call <> prettyArgs
         in BL.toStrict . toLazyByteString $ call_str <> lazyByteString ";\n"

data LlvmVar = LlvmVar SomePtr Term

instance CustomUserEvent LlvmVar where
    encodeUserEvent (LlvmVar ptr trm) = put ptr <> encodeMagicHeaderAndVersion (Version 1 1 0) <> encodeTerm trm
    decodeUserEvent = LlvmVar <$> get <*> decodeTerm' Nothing
    userEventTag _ = "LLVMV"
    eventType _ = LlvmCalls
    prettyPrintUserEvent (LlvmVar (SomePtr ptr) trm) = "/* " <> ptr <> " |-> " <> BS.pack (KPretty.renderDefault $ pretty trm) <> " */\n"

{- | Uses dlopen to load a .so/.dylib C library at runtime. For doucmentation of flags such as `RTL_LAZY`, consult e.g.
     https://man7.org/linux/man-pages/man3/dlopen.3.html
-}
withDLib :: FilePath -> (Linker.DL -> IO a) -> IO a
withDLib dlib = Linker.withDL dlib [Linker.RTLD_LAZY]

runLLVM :: API -> LLVM a -> IO a
runLLVM api (LLVM m) = runReaderT m api

mkAPI :: Linker.DL -> IO API
mkAPI dlib = flip runReaderT dlib $ do
    freePattern <- {-# SCC "LLVM.pattern.free" #-} korePatternFreeFunPtr

    newCompositePattern <- koreCompositePatternNew
    let newPattern name =
            {-# SCC "LLVM.pattern.new" #-}
            BS.useAsCString name $
                newCompositePattern
                    >=> newForeignPtr freePattern
                    >=> traceCall "kore_composite_pattern_new" [LlvmCallArgByteString name] "kore_pattern*"

    addArgumentCompositePattern <- koreCompositePatternAddArgument
    let addArgumentPattern parent child =
            {-# SCC "LLVM.pattern.addArgument" #-}
            do
                withForeignPtr parent $ \rawParent -> withForeignPtr child $ addArgumentCompositePattern rawParent
                finalizeForeignPtr child
                Trace.traceIO $
                    LlvmCall
                        { call = "kore_composite_pattern_add_argument"
                        , args = [LlvmCallArgPtr $ somePtr parent, LlvmCallArgPtr $ somePtr child]
                        , ret = Nothing
                        }
                pure parent

    newString <- koreStringPatternNewWithLen
    let string = KoreStringPatternAPI $ \name ->
            {-# SCC "LLVM.pattern.string" #-}
            BS.useAsCStringLen name $ \(rawStr, len) ->
                newString rawStr (fromIntegral len)
                    >>= ( newForeignPtr freePattern
                            >=> traceCall "kore_string_pattern_new_with_len" [LlvmCallArgByteString name] "kore_pattern*"
                        )

    newToken <- korePatternNewTokenWithLen
    let token = KoreTokenPatternAPI $ \name sort ->
            {-# SCC "LLVM.pattern.token" #-}
            BS.useAsCStringLen name $ \(rawName, len) ->
                withForeignPtr sort $
                    newToken rawName (fromIntegral len)
                        >=> newForeignPtr freePattern
                        >=> traceCall
                            "kore_pattern_new_token_with_len"
                            [LlvmCallArgByteString name, LlvmCallArgWord . fromIntegral $ len, LlvmCallArgPtr $ somePtr sort]
                            "kore_pattern*"

    compositePatternFromSymbol <- koreCompositePatternFromSymbol
    let fromSymbol sym =
            {-# SCC "LLVM.pattern.fromSymbol" #-}
            withForeignPtr sym $
                compositePatternFromSymbol
                    >=> newForeignPtr freePattern
                    >=> traceCall "kore_composite_pattern_from_symbol" [LlvmCallArgPtr $ somePtr sym] "kore_pattern*"

    dumpPattern' <- korePatternDump
    let dumpPattern ptr =
            {-# SCC "LLVM.pattern.dump" #-}
            withForeignPtr ptr $ \rawPtr -> do
                strPtr <- dumpPattern' rawPtr
                str <- C.peekCString strPtr
                Foreign.free strPtr
                pure str

    let patt =
            KorePatternAPI
                { new = newPattern
                , addArgument = addArgumentPattern
                , string
                , token
                , fromSymbol
                , dump = dumpPattern
                }

    freeSymbol <- {-# SCC "LLVM.symbol.free" #-} koreSymbolFreeFunPtr

    newSymbol' <- koreSymbolNew
    let newSymbol name =
            {-# SCC "LLVM.symbol.new" #-}
            liftIO $
                BS.useAsCString name $
                    newSymbol'
                        >=> newForeignPtr freeSymbol
                        >=> traceCall "kore_symbol_new" [LlvmCallArgByteString name] "kore_symbol*"

    addArgumentSymbol' <- koreSymbolAddFormalArgument
    let addArgumentSymbol sym sort =
            {-# SCC "LLVM.symbol.addArgument" #-}
            do
                withForeignPtr sym $ \rawSym -> withForeignPtr sort $ addArgumentSymbol' rawSym
                Trace.traceIO $
                    LlvmCall
                        { call = "kore_symbol_add_formal_argument"
                        , args = [LlvmCallArgPtr $ somePtr sym, LlvmCallArgPtr $ somePtr sort]
                        , ret = Nothing
                        }
                pure sym

    symbolCache <- liftIO $ newIORef mempty

    let symbol = KoreSymbolAPI{new = newSymbol, addArgument = addArgumentSymbol, cache = symbolCache}

    freeSort <- {-# SCC "LLVM.sort.free" #-} koreSortFreeFunPtr

    newSort' <- koreCompositeSortNew
    let newSort name =
            {-# SCC "LLVM.sort.new" #-}
            BS.useAsCString name $
                newSort'
                    >=> newForeignPtr freeSort
                    >=> traceCall "kore_composite_sort_new" [LlvmCallArgByteString name] "kore_sort*"

    addArgumentSort' <- koreCompositeSortAddArgument
    let addArgumentSort parent child =
            {-# SCC "LLVM.sort.addArgument" #-}
            do
                withForeignPtr parent $ \rawParent -> withForeignPtr child $ addArgumentSort' rawParent
                Trace.traceIO $
                    LlvmCall
                        { call = "kore_composite_sort_add_formal_argument"
                        , args = [LlvmCallArgPtr $ somePtr parent, LlvmCallArgPtr $ somePtr child]
                        , ret = Nothing
                        }
                pure parent

    dumpSort' <- koreSortDump
    let dumpSort ptr =
            {-# SCC "LLVM.sort.dump" #-}
            liftIO $ withForeignPtr ptr $ \rawPtr -> do
                strPtr <- dumpSort' rawPtr
                str <- C.peekCString strPtr
                Foreign.free strPtr
                pure str

    sortCache <- liftIO $ newIORef mempty

    let sort = KoreSortAPI{new = newSort, addArgument = addArgumentSort, dump = dumpSort, cache = sortCache}

    simplifyBool' <- koreSimplifyBool
    let simplifyBool p =
            {-# SCC "LLVM.simplifyBool" #-}
            do
                Trace.traceIO $
                    LlvmCall
                        { call = "kore_simplify_bool"
                        , args = [LlvmCallArgPtr $ somePtr p]
                        , ret = Nothing
                        }
                withForeignPtr p $ fmap (== 1) <$> simplifyBool'

    simplify' <- koreSimplify
    let simplify pat srt =
            {-# SCC "LLVM.simplify" #-}
            liftIO $
                withForeignPtr pat $ \patPtr ->
                    withForeignPtr srt $ \sortPtr ->
                        alloca $ \lenPtr ->
                            alloca $ \strPtr -> do
                                simplify' patPtr sortPtr strPtr lenPtr
                                Trace.traceIO $
                                    LlvmCall
                                        { call = "kore_simplify"
                                        , args =
                                            [ LlvmCallArgPtr $ somePtr patPtr
                                            , LlvmCallArgPtr $ somePtr sortPtr
                                            , LlvmCallArgPtr $ somePtr strPtr
                                            , LlvmCallArgPtr $ somePtr lenPtr
                                            ]
                                        , ret = Nothing
                                        }
                                len <- fromIntegral <$> peek lenPtr
                                cstr <- peek strPtr
                                result <- BS.packCStringLen (cstr, len)
                                Foreign.free cstr
                                pure result

    pure API{patt, symbol, sort, simplifyBool, simplify}
  where
    traceCall call args retTy retPtr = do
        Trace.traceIO $ LlvmCall{ret = Just (retTy, somePtr retPtr), call, args}
        pure retPtr

ask :: LLVM API
ask = LLVM Reader.ask

marshallSymbol :: Symbol -> [Sort] -> LLVM KoreSymbolPtr
marshallSymbol sym sorts = do
    kore <- ask
    cache <- liftIO $ readIORef kore.symbol.cache
    case HM.lookup (sym, sorts) cache of
        Just ptr -> pure ptr
        Nothing -> do
            sym' <- liftIO $ kore.symbol.new sym.name
            liftIO $ modifyIORef' kore.symbol.cache $ HM.insert (sym, sorts) sym'
            foldM (\symbol sort -> marshallSort sort >>= liftIO . kore.symbol.addArgument symbol) sym' sorts

marshallSort :: Sort -> LLVM KoreSortPtr
marshallSort = \case
    s@(SortApp name args) -> do
        kore <- ask
        cache <- liftIO $ readIORef kore.sort.cache
        case HM.lookup s cache of
            Just ptr -> pure ptr
            Nothing -> do
                sort <- liftIO $ kore.sort.new name
                forM_ args $ marshallSort >=> liftIO . kore.sort.addArgument sort
                liftIO $ modifyIORef' kore.sort.cache $ HM.insert s sort
                pure sort
    SortVar varName -> error $ "marshalling SortVar " <> show varName <> " unsupported"

marshallTerm :: Term -> LLVM KorePatternPtr
marshallTerm t = do
    kore <- ask
    case t of
        SymbolApplication symbol sorts trms -> do
            trm <- liftIO . kore.patt.fromSymbol =<< marshallSymbol symbol sorts
            forM_ trms $ marshallTerm >=> liftIO . kore.patt.addArgument trm
            pure trm
        AndTerm l r -> do
            andSym <- liftIO $ kore.symbol.new "\\and"
            void $ liftIO . kore.symbol.addArgument andSym =<< marshallSort (sortOfTerm l)
            trm <- liftIO $ kore.patt.fromSymbol andSym
            void $ liftIO . kore.patt.addArgument trm =<< marshallTerm l
            liftIO . kore.patt.addArgument trm =<< marshallTerm r
        DomainValue sort val ->
            marshallSort sort >>= liftIO . kore.patt.token.new val
        Var varName -> error $ "marshalling Var " <> show varName <> " unsupported"
        Injection source target trm -> do
            inj <- liftIO . kore.patt.fromSymbol =<< marshallSymbol injectionSymbol [source, target]
            marshallTerm trm >>= liftIO . kore.patt.addArgument inj
        KMap def keyVals rest -> marshallTerm $ externaliseKmapUnsafe def keyVals rest
