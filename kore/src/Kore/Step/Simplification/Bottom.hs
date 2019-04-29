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

import           Kore.AST.MetaOrObject
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Syntax.Bottom

{-| simplifies a Bottom pattern, which means returning an always-false or.
-}
simplify
    :: Ord variable
    => Bottom Object child
    -> (OrPattern Object variable, SimplificationProof Object)
simplify Bottom {} = (OrPattern.bottom, SimplificationProof)
