{-|
Module      : Kore.Step.Simplification.Top
Description : Tools for Top pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Top
    ( simplify
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Variable
import Kore.Sort
import Kore.Syntax.Top

{-| simplifies a Top pattern, which means returning an always-true or.
-}
-- TODO (virgil): Preserve pattern sorts under simplification.
simplify
    :: InternalVariable variable
    => Top Sort child
    -> OrPattern variable
simplify _ = OrPattern.top
