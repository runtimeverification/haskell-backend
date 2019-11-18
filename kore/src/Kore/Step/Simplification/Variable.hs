{-|
Module      : Kore.Step.Simplification.Variable
Description : Tools for Variable pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Variable
    ( simplify
    ) where

import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromTermLike
    )
import Kore.Variables.UnifiedVariable

{-| 'simplify' simplifies a 'Variable' pattern, which means returning
an or containing a term made of that variable.
-}
simplify
    :: InternalVariable variable
    => UnifiedVariable variable
    -> Simplifiable variable
simplify var = Simplifiable.fromTermLike $ mkVar var
