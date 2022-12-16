{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -ddump-splices #-}

module Kore.LLVM.Internal (API (..), KorePatternAPI (..), runLLVM, runLLVMwithDL, withDLib, ask, marshallTerm) where

import Control.Monad (forM_, void, (>=>))
import Control.Monad.IO.Class (MonadIO (..))
import Control.Monad.Trans.Reader (ReaderT (runReaderT))
import Control.Monad.Trans.Reader qualified as Reader
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Foreign (ForeignPtr, finalizeForeignPtr, newForeignPtr, withForeignPtr)
import Foreign qualified
import Foreign.C qualified as C
import Kore.LLVM.TH (dynamicBindings)
import Kore.Pattern.Base
import Kore.Pattern.Util (applySubst, sortOfTerm)
import System.Posix.DynamicLinker qualified as Linker

data KorePattern
data KoreSort
data KoreSymbol
data Block

type KorePatternPtr = ForeignPtr KorePattern
type KoreSymbolPtr = ForeignPtr KoreSymbol
type KoreSortPtr = ForeignPtr KoreSort

$(dynamicBindings "./cbits/kllvm-c.h")

newtype KoreStringPatternAPI = KoreStringPatternAPI
    { new :: Text -> LLVM KorePatternPtr
    }

newtype KoreTokenPatternAPI = KoreTokenPatternAPI
    { new :: Text -> KoreSortPtr -> LLVM KorePatternPtr
    }

data KoreSymbolAPI = KoreSymbolAPI
    { new :: Text -> LLVM KoreSymbolPtr
    , addArgument :: KoreSymbolPtr -> KoreSortPtr -> LLVM KoreSymbolPtr
    }

data KoreSortAPI = KoreSortAPI
    { new :: Text -> LLVM KoreSortPtr
    , addArgument :: KoreSortPtr -> KoreSortPtr -> LLVM KoreSortPtr
    , dump :: KoreSortPtr -> LLVM String
    }

data KorePatternAPI = KorePatternAPI
    { new :: Text -> LLVM KorePatternPtr
    , addArgument :: KorePatternPtr -> KorePatternPtr -> LLVM KorePatternPtr
    , fromSymbol :: KoreSymbolPtr -> LLVM KorePatternPtr
    , string :: KoreStringPatternAPI
    , token :: KoreTokenPatternAPI
    , dump :: KorePatternPtr -> LLVM String
    }

data API = API
    { patt :: KorePatternAPI
    , symbol :: KoreSymbolAPI
    , sort :: KoreSortAPI
    , simplifyBool :: KorePatternPtr -> LLVM Bool
    }

newtype LLVM a = LLVM (ReaderT API IO a)
    deriving newtype (Functor, Applicative, Monad, MonadIO)

{- | Uses dlopen to load a .so/.dylib C library at runtime. For doucmentation of flags such as `RTL_LAZY`, consult e.g.
     https://man7.org/linux/man-pages/man3/dlopen.3.html
-}
withDLib :: FilePath -> (Linker.DL -> IO a) -> IO a
withDLib dlib = Linker.withDL dlib [Linker.RTLD_LAZY]

runLLVM :: FilePath -> LLVM a -> IO a
runLLVM fp m = withDLib fp $ flip runLLVMwithDL m

runLLVMwithDL :: Linker.DL -> LLVM a -> IO a
runLLVMwithDL dlib (LLVM m) = flip runReaderT dlib $ do
    patt <- do
        freePattern <- korePatternFreeFunPtr

        newCompositePattern <- koreCompositePatternNew
        let new name =
                liftIO $
                    C.withCString (Text.unpack name) $
                        newCompositePattern >=> newForeignPtr freePattern

        addArgumentCompositePattern <- koreCompositePatternAddArgument
        let addArgument parent child = liftIO $ do
                withForeignPtr parent $ \rawParent -> withForeignPtr child $ addArgumentCompositePattern rawParent
                finalizeForeignPtr child
                pure parent

        string <- do
            newString <- koreStringPatternNew
            pure $ KoreStringPatternAPI $ \name -> liftIO $ C.withCString (Text.unpack name) $ newString >=> newForeignPtr freePattern

        token <- do
            newToken <- korePatternNewToken
            pure $ KoreTokenPatternAPI $ \name sort -> liftIO $ C.withCString (Text.unpack name) $ \rawName ->
                withForeignPtr sort $
                    newToken rawName >=> newForeignPtr freePattern

        fromSymbol <- do
            compositePatternFromSymbol <- koreCompositePatternFromSymbol
            pure $ \sym -> liftIO $ withForeignPtr sym $ compositePatternFromSymbol >=> newForeignPtr freePattern

        dump <- do
            dump' <- korePatternDump
            pure $ \ptr -> liftIO $ withForeignPtr ptr $ \rawPtr -> do
                strPtr <- dump' rawPtr
                str <- C.peekCString strPtr
                Foreign.free strPtr
                pure str
        pure KorePatternAPI{new, addArgument, string, token, fromSymbol, dump}

    symbol <- do
        freeSymbol <- koreSymbolFreeFunPtr

        newSymbol <- koreSymbolNew
        let new name =
                liftIO $
                    C.withCString (Text.unpack name) $
                        newSymbol >=> newForeignPtr freeSymbol

        addArgumentSymbol <- koreSymbolAddFormalArgument
        let addArgument sym sort = liftIO $ do
                withForeignPtr sym $ \rawSym -> withForeignPtr sort $ addArgumentSymbol rawSym
                pure sym

        pure KoreSymbolAPI{new, addArgument}

    sort <- do
        freeSort <- koreSortFreeFunPtr

        newSort <- koreCompositeSortNew
        let new name =
                liftIO $
                    C.withCString (Text.unpack name) $
                        newSort >=> newForeignPtr freeSort

        addArgumentSort <- koreCompositeSortAddArgument
        let addArgument parent child = liftIO $ do
                withForeignPtr parent $ \rawParent -> withForeignPtr child $ addArgumentSort rawParent
                pure parent

        dump <- do
            dump' <- koreSortDump
            pure $ \ptr -> liftIO $ withForeignPtr ptr $ \rawPtr -> do
                strPtr <- dump' rawPtr
                str <- C.peekCString strPtr
                Foreign.free strPtr
                pure str

        pure KoreSortAPI{new, addArgument, dump}

    simplifyBool <- do
        simplify <- koreSimplifyBool
        pure $ \p -> liftIO $ withForeignPtr p $ fmap (== 1) <$> simplify

    liftIO $ runReaderT m $ API{patt, symbol, sort, simplifyBool}

ask :: LLVM API
ask = LLVM Reader.ask

marshallSymbol :: Symbol -> [Sort] -> LLVM KoreSymbolPtr
marshallSymbol sym sorts = do
    kore <- ask
    sym' <- kore.symbol.new sym.name
    forM_ sym.argSorts $ marshallSort . applySorts >=> kore.symbol.addArgument sym'
    kore.symbol.addArgument sym' =<< marshallSort sym.resultSort
  where
    applySorts = applySubst (Map.fromList $ zip sym.sortVars sorts)

marshallSort :: Sort -> LLVM KoreSortPtr
marshallSort = \case
    SortApp name args -> do
        kore <- ask
        sort <- kore.sort.new name
        forM_ args $ marshallSort >=> kore.sort.addArgument sort
        pure sort
    SortVar _ -> error "marshalling SortVar unsupported"

marshallTerm :: Term -> LLVM KorePatternPtr
marshallTerm t = do
    kore <- ask
    case t of
        SymbolApplication symbol sorts trms -> do
            trm <- kore.patt.fromSymbol =<< marshallSymbol symbol sorts
            forM_ trms $ marshallTerm >=> kore.patt.addArgument trm
            pure trm
        AndTerm l r -> do
            andSym <- kore.symbol.new "\\and"
            void $ kore.symbol.addArgument andSym =<< marshallSort (sortOfTerm l)
            trm <- kore.patt.fromSymbol andSym
            void $ kore.patt.addArgument trm =<< marshallTerm l
            kore.patt.addArgument trm =<< marshallTerm r
        DomainValue sort val ->
            marshallSort sort >>= kore.patt.token.new val
        Var _ -> error "marshalling Var unsupported"
