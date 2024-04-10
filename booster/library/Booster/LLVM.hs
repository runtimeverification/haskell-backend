module Booster.LLVM (simplifyBool, simplifyTerm) where

import Control.Monad.IO.Class (MonadIO (..))
import Data.Binary.Get
import Data.ByteString (fromStrict)
import Data.Map qualified as Map
import Data.Set qualified as Set

import Booster.Definition.Base
import Booster.LLVM.Internal qualified as Internal
import Booster.Pattern.Base
import Booster.Pattern.Binary
import Booster.Pattern.Util
import Booster.Trace qualified as Trace
import Data.ByteString.Char8 qualified as BS

simplifyBool :: MonadIO io => Internal.API -> Term -> io (Either Internal.LlvmError Bool)
simplifyBool api trm = liftIO $ Internal.runLLVM api $ do
    kore <- Internal.ask
    trmPtr <- Trace.timeIO "LLVM.simplifyBool.marshallTerm" (Internal.marshallTerm trm)

    Trace.traceIO $ Internal.LlvmVar (Internal.somePtr trmPtr) trm

    liftIO $ kore.simplifyBool trmPtr

simplifyTerm ::
    MonadIO io => Internal.API -> KoreDefinition -> Term -> Sort -> io (Either Internal.LlvmError Term)
simplifyTerm api def trm sort = liftIO $ Internal.runLLVM api $ do
    kore <- Internal.ask
    trmPtr <- Trace.timeIO "LLVM.simplifyTerm.marshallTerm" $ Internal.marshallTerm trm
    sortPtr <- Trace.timeIO "LLVM.simplifyTerm.marshallSort" $ Internal.marshallSort sort
    mbinary <- liftIO $ kore.simplify trmPtr sortPtr
    liftIO kore.collect
    Trace.traceIO $ Internal.LlvmVar (Internal.somePtr trmPtr) trm
    case mbinary of
        Left err -> pure $ Left err
        Right binary -> do
            -- strip away the custom injection added by the LLVM backend
            Trace.timeIO "LLVM.simplifyTerm.decodeTerm" $ case runGet (decodeTerm def) (fromStrict binary) of
                result
                    | sortOfTerm result == sort ->
                        pure $ Right result
                    | newSort@(SortApp name _) <- sortOfTerm result
                    , Set.member name subsorts ->
                        pure $ Right $ Injection newSort sort result
                    | otherwise -> do
                        pure $
                            Left $
                                Internal.LlvmError $
                                    BS.pack $
                                        "LLVM simplification returned sort  "
                                            <> show (sortOfTerm result)
                                            <> ". Expected sort "
                                            <> show sort
  where
    sortName (SortApp name _) = name
    sortName (SortVar name) = name
    subsorts = maybe Set.empty snd $ Map.lookup (sortName sort) def.sorts
