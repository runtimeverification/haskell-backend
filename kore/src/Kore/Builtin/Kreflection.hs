{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Builtin.Kreflection (
    verifiers,
) where

import Data.HashMap.Strict qualified as HashMap
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Error qualified
import Prelude.Kore

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers = mempty
        , symbolVerifiers
        , patternVerifierHook = mempty
        }

symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
        [ ("KREFLECTION.isConcrete", rejectSymbolIsConcrete)
        ]

rejectSymbolIsConcrete :: Builtin.SymbolVerifier
rejectSymbolIsConcrete =
    Builtin.SymbolVerifier $ \_ _ ->
        Kore.Error.koreFail "found KREFLECTION.isConcrete hook"
