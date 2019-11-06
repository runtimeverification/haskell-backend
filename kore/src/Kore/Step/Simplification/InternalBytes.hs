{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.InternalBytes
    ( simplify
    ) where

import Kore.Internal.InternalBytes
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( fromTermLike
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    )

simplify :: SimplifierVariable variable => InternalBytes -> Pattern variable
simplify = Pattern.fromTermLike . mkInternalBytes'
