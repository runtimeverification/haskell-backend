{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Booster.LLVM (simplifyBool, simplifyTerm) where

import Control.Monad.IO.Class (MonadIO (..))
import Data.Binary.Get
import Data.ByteString (fromStrict)
import System.IO.Unsafe (unsafePerformIO)

import Booster.Definition.Base
import Booster.LLVM.Internal qualified as Internal
import Booster.Pattern.Base
import Booster.Pattern.Binary
import Booster.Trace qualified as Trace

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
    liftIO kore.collect
    Trace.traceIO $ Internal.LlvmVar (Internal.somePtr trmPtr) trm
    Trace.timeIO "LLVM.simplifyTerm.decodeTerm" $
        pure (runGet (decodeTerm def) (fromStrict binary))
