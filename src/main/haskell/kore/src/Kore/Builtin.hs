{- |
Module      : Kore.Builtin
Description : Built-in sorts and symbols
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified.

@
    import qualified Kore.Builtin as Builtin
@
 -}
module Kore.Builtin
    ( Verifiers (..)
    , sortVerifier
    , symbolVerifier
    , koreBuiltins
    ) where

import Data.Semigroup ( (<>) )

import qualified Kore.Builtin.Bool as Bool
import           Kore.Builtin.Builtin
                 ( Verifiers (..), sortVerifier, symbolVerifier )
import qualified Kore.Builtin.Int as Int

{- | Verifiers for Kore builtin sorts.

  If you aren't sure which verifiers you need, use these.

 -}
koreBuiltins :: Verifiers
koreBuiltins =
    Verifiers
    { sortVerifiers =
           Bool.sortVerifiers
        <> Int.sortVerifiers
    , symbolVerifiers =
           Bool.symbolVerifiers
        <> Int.symbolVerifiers
    , patternVerifiers =
           Bool.patternVerifiers
        <> Int.patternVerifiers
    }
