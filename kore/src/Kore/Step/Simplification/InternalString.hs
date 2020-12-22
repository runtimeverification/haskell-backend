{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.InternalString
    ( simplify
    ) where

import Prelude.Kore

import Kore.Internal.InternalString
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike

simplify
    :: InternalVariable variable
    => InternalString
    -> OrPattern variable
simplify = OrPattern.fromPattern . pure . mkInternalString
