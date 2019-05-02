{-|
Module      : Kore.Step.Simplification.Inhabitant
Description : Tools for Inhabitant pattern simplification.
Copyright   : (c) Runtime Verification, 2018
-}
module Kore.Step.Simplification.Inhabitant
    ( simplify
    ) where

import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.TermLike

{-| 'simplify' simplifies a 'StringLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify
    :: (Ord variable, SortedVariable variable)
    => Sort
    -> OrPattern variable
simplify s = OrPattern.fromTermLike $ mkInhabitant s
