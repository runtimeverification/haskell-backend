{-# LANGUAGE Strict #-}

{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Step.Simplification.InternalBytes (
    simplify,
) where

import Prelude.Kore

import Kore.Internal.InternalBytes
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )

simplify ::
    InternalBytes ->
    OrPattern RewritingVariableName
simplify = OrPattern.fromPattern . pure . mkInternalBytes'
