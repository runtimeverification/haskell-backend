{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -ddump-splices #-}

module Kore.LLVM.Internal (API (..), KorePatternAPI (..), runLLVM, ask, marshallTerm) where

import Control.Monad (foldM, (>=>))
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Control.Monad.Trans.Reader qualified as Reader
import Data.Text (Text)
import Data.Text qualified as Text
import Foreign (ForeignPtr, finalizeForeignPtr, newForeignPtr, withForeignPtr)
import Foreign qualified
import Foreign.C qualified as C
import Kore.LLVM.TH (dynamicBindings)
import Kore.Pattern.Base
import System.Posix.DynamicLinker qualified as Linker

data KorePattern
type KorePatternPtr = ForeignPtr KorePattern

$(dynamicBindings "./cbits/kllvm-c.h")

data KoreCompositePatternAPI = KoreCompositePatternAPI
    { new :: Text -> LLVM KorePatternPtr
    , addArgument :: KorePatternPtr -> KorePatternPtr -> LLVM KorePatternPtr
    }

newtype KoreStringPatternAPI = KoreStringPatternAPI
    { new :: Text -> LLVM KorePatternPtr
    }

data KorePatternAPI = KorePatternAPI
    { composite :: KoreCompositePatternAPI
    , string :: KoreStringPatternAPI
    , dump :: KorePatternPtr -> LLVM String
    }

newtype API = API
    { korePattern :: KorePatternAPI
    }

newtype LLVM a = LLVM (ReaderT API IO a)
    deriving newtype (Functor, Applicative, Monad, MonadIO)

{- | Uses dlopen to load a .so/.dylib C library at runtime. For doucmentation of flags such as `RTL_LAZY`, consult e.g.
     https://man7.org/linux/man-pages/man3/dlopen.3.html
-}
withDLib :: FilePath -> ReaderT Linker.DL IO a -> IO a
withDLib dlib = Linker.withDL dlib [Linker.RTLD_LAZY] . runReaderT

runLLVM :: FilePath -> LLVM a -> IO a
runLLVM dlib (LLVM m) = withDLib dlib $ do
    free <- korePatternFreeFunPtr
    composite <- do
        new' <- koreCompositePatternNew
        let new name =
                liftIO $
                    C.withCString (Text.unpack name) $
                        new' >=> newForeignPtr free

        addArgument' <- koreCompositePatternAddArgument
        let addArgument parent child = liftIO $ do
                withForeignPtr parent $ \rawParent -> withForeignPtr child $ addArgument' rawParent
                finalizeForeignPtr child
                pure parent

        pure KoreCompositePatternAPI{new, addArgument}

    string <- do
        new <- koreStringPatternNew
        pure $ KoreStringPatternAPI $ \name -> liftIO $ C.withCString (Text.unpack name) $ new >=> newForeignPtr free

    dump <- do
        dump' <- korePatternDump
        pure $ \ptr -> liftIO $ withForeignPtr ptr $ \rawPtr -> do
            strPtr <- dump' rawPtr
            str <- C.peekCString strPtr
            Foreign.free strPtr
            pure str

    liftIO $ runReaderT m $ API KorePatternAPI{composite, string, dump}

ask :: LLVM API
ask = LLVM Reader.ask

marshallTerm :: Term -> LLVM KorePatternPtr
marshallTerm = \case
    SymbolApplication symbol trms -> do
        api <- ask
        app <- api.korePattern.composite.new symbol.name
        foldM (\app' t -> api.korePattern.composite.addArgument app' =<< marshallTerm t) app trms
    AndTerm _ _ -> error "marshalling And undefined"
    DomainValue _sort val -> do
        api <- ask
        api.korePattern.string.new val
    Var _ -> error "marshalling Var undefined"
