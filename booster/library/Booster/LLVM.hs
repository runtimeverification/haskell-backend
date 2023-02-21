module Booster.LLVM (simplifyBool, simplifyTerm) where

import Booster.Definition.Base
import Booster.LLVM.Internal qualified as Internal
import Booster.Pattern.Base
import Booster.Pattern.Binary
import Booster.Pattern.Util
import Booster.Trace qualified as Trace
import Control.Monad.IO.Class (MonadIO (..))
import Data.Binary.Get
import Data.ByteString (fromStrict)
import System.IO.Unsafe (unsafePerformIO)

simplifyBool :: Internal.API -> Term -> Bool
simplifyBool api trm = unsafePerformIO $ Internal.runLLVM api $ do
    kore <- Internal.ask
    trmPtr <- Trace.timeIO "LLVM.simplifyBool.marshallTerm" (Internal.marshallTerm trm)

    Trace.traceIO $ Internal.LlvmVar (Internal.somePtr trmPtr) trm

    liftIO $ kore.simplifyBool trmPtr

simplifyTerm :: Internal.API -> KoreDefinition -> Term -> Sort -> Term
simplifyTerm api def trm sort = unsafePerformIO $ Internal.runLLVM api $ do
    kore <- Internal.ask
    trmPtr <- Trace.timeIO "LLVM.simplifyTerm.marshallTerm" $ Internal.marshallTerm trm
    sortPtr <- Trace.timeIO "LLVM.simplifyTerm.marshallSort" $ Internal.marshallSort sort
    binary <- liftIO $ kore.simplify trmPtr sortPtr
    Trace.traceIO $ Internal.LlvmVar (Internal.somePtr trmPtr) trm
    -- strip away the custom injection added by the LLVM backend
    Trace.timeIO "LLVM.simplifyTerm.decodeTerm" $ case runGet (decodeTerm def) (fromStrict binary) of
        Injection origSort (SortApp "SortKItem" _) result
            | origSort == sort ->
                pure result
        someTerm
            | sortOfTerm someTerm == sort ->
                pure someTerm
        other ->
            error $ "Unexpected sort after LLVM simplification: " <> show other
