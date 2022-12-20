module Kore.LLVM (simplifyBool, simplifyTerm) where

import Kore.LLVM.Internal qualified as Internal
import Kore.Pattern.Base

import Data.Binary.Get
import Data.ByteString (fromStrict)
import Kore.Definition.Base
import Kore.Pattern.Binary
import System.IO.Unsafe (unsafePerformIO)
import System.Posix.DynamicLinker qualified as Linker

simplifyBool :: Linker.DL -> Term -> Bool
simplifyBool dl trm = unsafePerformIO $ Internal.runLLVMwithDL dl $ do
    kore <- Internal.ask
    Internal.marshallTerm trm >>= kore.simplifyBool

simplifyTerm :: Linker.DL -> KoreDefinition -> Term -> Sort -> Term
simplifyTerm dl def trm sort = unsafePerformIO $ Internal.runLLVMwithDL dl $ do
    kore <- Internal.ask
    trmPtr <- Internal.marshallTerm trm
    sortPtr <- Internal.marshallSort sort
    binary <- kore.simplify trmPtr sortPtr
    pure $ runGet (decodeKorePattern def) $ fromStrict binary
