{-|
Module      : Kore.Step.Simplification.Bottom
Description : Tools for Bottom pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Bottom
    ( simplify
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Sort
import Kore.Syntax.Bottom

{-| simplifies a Bottom pattern, which means returning an always-false or.
-}
simplify :: Ord variable => Bottom Sort child -> OrPattern variable
simplify Bottom {} = OrPattern.bottom
