{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.InternalBytes
    ( simplify
    ) where

import Kore.Internal.InternalBytes
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromTermLike
    )
import Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    )

simplify
    :: SimplifierVariable variable => InternalBytes -> Simplifiable variable
simplify =
    Simplifiable.fromTermLike . mkInternalBytes'
