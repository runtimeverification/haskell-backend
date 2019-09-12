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

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike

{-| 'simplify' simplifies a 'Variable' pattern, which means returning
an or containing a term made of that variable.
-}
simplify
    :: InternalVariable variable
    => SetVariable variable
    -> OrPattern variable
simplify setVar = OrPattern.fromTermLike $ mkSetVar setVar
