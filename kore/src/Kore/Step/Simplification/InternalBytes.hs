{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.InternalBytes
    ( simplify
    ) where

import Prelude.Kore

import Kore.Internal.InternalBytes
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    )

simplify :: InternalVariable variable => InternalBytes -> OrPattern variable
simplify = pure . pure . mkInternalBytes'
