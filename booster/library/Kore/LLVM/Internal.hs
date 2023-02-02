{-# LANGUAGE StrictData #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

module Kore.LLVM.Internal (
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
) where

import Control.Monad (foldM, forM_, void, (>=>))
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Control.Monad.Trans.Reader qualified as Reader
import Data.ByteString (ByteString)
import Data.ByteString.Char8 (packCStringLen)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.IORef (IORef, modifyIORef', newIORef, readIORef)
import Data.Text (Text)
import Data.Text qualified as Text
import Foreign (ForeignPtr, finalizeForeignPtr, newForeignPtr, withForeignPtr)
import Foreign qualified
import Foreign.C qualified as C
import Foreign.C.Types (CSize (..))
import Foreign.Marshal (alloca)
import Foreign.Storable (peek)
import Kore.LLVM.TH (dynamicBindings)
import Kore.Pattern.Base
import Kore.Pattern.Util (sortOfTerm)
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
    { new :: Text -> IO KorePatternPtr
    }

newtype KoreTokenPatternAPI = KoreTokenPatternAPI
    { new :: Text -> KoreSortPtr -> IO KorePatternPtr
    }

data KoreSymbolAPI = KoreSymbolAPI
    { new :: Text -> IO KoreSymbolPtr
    , addArgument :: KoreSymbolPtr -> KoreSortPtr -> IO KoreSymbolPtr
    , cache :: IORef (HashMap (Symbol, [Sort]) KoreSymbolPtr)
    }

data KoreSortAPI = KoreSortAPI
    { new :: Text -> IO KoreSortPtr
    , addArgument :: KoreSortPtr -> KoreSortPtr -> IO KoreSortPtr
    , dump :: KoreSortPtr -> IO String
    , cache :: IORef (HashMap Sort KoreSortPtr)
    }

data KorePatternAPI = KorePatternAPI
    { new :: Text -> IO KorePatternPtr
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
    deriving newtype (Functor, Applicative, Monad, MonadIO)

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
            liftIO $
                C.withCString (Text.unpack name) $
                    newCompositePattern >=> newForeignPtr freePattern

    addArgumentCompositePattern <- koreCompositePatternAddArgument
    let addArgumentPattern parent child =
            liftIO $
                {-# SCC "LLVM.pattern.addArgument" #-}
                do
                    withForeignPtr parent $ \rawParent -> withForeignPtr child $ addArgumentCompositePattern rawParent
                    finalizeForeignPtr child
                    pure parent

    newString <- koreStringPatternNewWithLen
    let string = KoreStringPatternAPI $ \name ->
            {-# SCC "LLVM.pattern.string" #-}
            liftIO $ C.withCStringLen (Text.unpack name) $ \(rawStr, len) ->
                newString rawStr (fromIntegral len) >>= newForeignPtr freePattern

    newToken <- korePatternNewTokenWithLen
    let token = KoreTokenPatternAPI $ \name sort ->
            {-# SCC "LLVM.pattern.token" #-}
            liftIO $ C.withCStringLen (Text.unpack name) $ \(rawName, len) ->
                withForeignPtr sort $
                    newToken rawName (fromIntegral len) >=> newForeignPtr freePattern

    compositePatternFromSymbol <- koreCompositePatternFromSymbol
    let fromSymbol sym = {-# SCC "LLVM.pattern.fromSymbol" #-} liftIO $ withForeignPtr sym $ compositePatternFromSymbol >=> newForeignPtr freePattern

    dumpPattern' <- korePatternDump
    let dumpPattern ptr =
            {-# SCC "LLVM.pattern.dump" #-}
            liftIO $ withForeignPtr ptr $ \rawPtr -> do
                strPtr <- dumpPattern' rawPtr
                str <- C.peekCString strPtr
                Foreign.free strPtr
                pure str

    let patt = KorePatternAPI{new = newPattern, addArgument = addArgumentPattern, string, token, fromSymbol, dump = dumpPattern}

    freeSymbol <- {-# SCC "LLVM.symbol.free" #-} koreSymbolFreeFunPtr

    newSymbol' <- koreSymbolNew
    let newSymbol name =
            {-# SCC "LLVM.symbol.new" #-}
            liftIO $
                C.withCString (Text.unpack name) $
                    newSymbol' >=> newForeignPtr freeSymbol

    addArgumentSymbol' <- koreSymbolAddFormalArgument
    let addArgumentSymbol sym sort =
            liftIO $
                {-# SCC "LLVM.symbol.addArgument" #-}
                do
                    withForeignPtr sym $ \rawSym -> withForeignPtr sort $ addArgumentSymbol' rawSym
                    pure sym

    symbolCache <- liftIO $ newIORef mempty

    let symbol = KoreSymbolAPI{new = newSymbol, addArgument = addArgumentSymbol, cache = symbolCache}

    freeSort <- {-# SCC "LLVM.sort.free" #-} koreSortFreeFunPtr

    newSort' <- koreCompositeSortNew
    let newSort name =
            {-# SCC "LLVM.sort.new" #-}
            liftIO $
                C.withCString (Text.unpack name) $
                    newSort' >=> newForeignPtr freeSort

    addArgumentSort' <- koreCompositeSortAddArgument
    let addArgumentSort parent child =
            liftIO $
                {-# SCC "LLVM.sort.addArgument" #-}
                do
                    withForeignPtr parent $ \rawParent -> withForeignPtr child $ addArgumentSort' rawParent
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
    let simplifyBool p = {-# SCC "LLVM.simplifyBool" #-} liftIO $ withForeignPtr p $ fmap (== 1) <$> simplifyBool'

    simplify' <- koreSimplify
    let simplify pat srt =
            {-# SCC "LLVM.simplify" #-}
            liftIO $
                withForeignPtr pat $ \patPtr ->
                    withForeignPtr srt $ \sortPtr ->
                        alloca $ \lenPtr ->
                            alloca $ \strPtr -> do
                                simplify' patPtr sortPtr strPtr lenPtr
                                len <- fromIntegral <$> peek lenPtr
                                cstr <- peek strPtr
                                packCStringLen (cstr, len)

    pure API{patt, symbol, sort, simplifyBool, simplify}

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
