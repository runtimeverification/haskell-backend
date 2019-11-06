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

import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( fromTermLike
    )
import Kore.Internal.TermLike
import Kore.Variables.UnifiedVariable

{-| 'simplify' simplifies a 'Variable' pattern, which means returning
an or containing a term made of that variable.
-}
simplify
    :: InternalVariable variable
    => UnifiedVariable variable
    -> Pattern variable
simplify var = Pattern.fromTermLike $ mkVar var
