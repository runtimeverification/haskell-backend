module Kore.LLVM (simplifyBool) where

import Kore.LLVM.Internal qualified as Internal
import Kore.Pattern.Base

import System.IO.Unsafe (unsafePerformIO)
import System.Posix.DynamicLinker qualified as Linker

simplifyBool :: Linker.DL -> Term -> Bool
simplifyBool dl trm = unsafePerformIO $ Internal.runLLVMwithDL dl $ do
    kore <- Internal.ask
    Internal.marshallTerm trm >>= kore.simplifyBool
