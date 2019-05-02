{-|
Module      : Kore.Step.Simplification.SetVariable
Description : Tools for SetVariable pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.SetVariable
    ( simplify
    ) where

import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.TermLike
import           Kore.Syntax.SetVariable

{-| 'simplify' simplifies a 'Variable' pattern, which means returning
an or containing a term made of that variable.
-}
simplify
    :: (Ord variable, SortedVariable variable)
    => SetVariable variable
    -> OrPattern variable
simplify (SetVariable var) = OrPattern.fromTermLike $ mkSetVar var
