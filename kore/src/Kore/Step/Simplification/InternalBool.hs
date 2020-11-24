{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.InternalBool
    ( simplify
    ) where

import Prelude.Kore

import Kore.Internal.InternalBool
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike

simplify
    :: InternalVariable variable
    => InternalBool
    -> OrPattern variable
simplify = OrPattern.fromPattern . pure . mkInternalBool
