{- |
Module      : Kore.Step.Simplification.StringLiteral
Description : Tools for StringLiteral pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.StringLiteral (
    simplify,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

{- | 'simplify' simplifies a 'StringLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify :: StringLiteral -> OrPattern RewritingVariableName
simplify (StringLiteral str) = OrPattern.fromTermLike $ mkStringLiteral str
