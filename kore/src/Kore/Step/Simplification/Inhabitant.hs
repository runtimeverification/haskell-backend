{-|
Module      : Kore.Step.Simplification.Inhabitant
Description : Tools for Inhabitant pattern simplification.
Copyright   : (c) Runtime Verification, 2018
-}
module Kore.Step.Simplification.Inhabitant
    ( simplify
    ) where

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.TermLike

{-| 'simplify' simplifies a 'StringLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify
    :: (Ord variable, SortedVariable variable)
    => Inhabitant (OrPattern variable)
    -> OrPattern variable
simplify Inhabitant { inhSort } = OrPattern.fromTermLike $ mkInhabitant inhSort
