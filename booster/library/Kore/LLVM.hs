module Kore.LLVM (simplifyBool, simplifyTerm) where

import Kore.LLVM.Internal qualified as Internal
import Kore.Pattern.Base

import Data.Binary.Get
import Data.ByteString (fromStrict)
import Kore.Definition.Base
import Kore.Pattern.Binary
import Kore.Pattern.Util
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
    -- strip away the custom injection added by the LLVM backend
    case runGet (decodeKorePattern def) (fromStrict binary) of
        Injection origSort (SortApp "SortKItem" _) result
            | origSort == sort ->
                pure result
        someTerm
            | sortOfTerm someTerm == sort ->
                pure someTerm
        other ->
            error $ "Unexpected sort after LLVM simplification: " <> show other
