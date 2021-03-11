{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
{-# LANGUAGE Strict #-}

module Kore.Step.Simplification.InternalInt
    ( simplify
    ) where

import Prelude.Kore

import Kore.Internal.InternalInt
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )

simplify
    :: InternalInt
    -> OrPattern RewritingVariableName
simplify = OrPattern.fromPattern . pure . mkInternalInt
