{- |
Module      : Kore.Simplify.Inhabitant
Description : Tools for Inhabitant pattern simplification.
Copyright   : (c) Runtime Verification, 2018
-}
module Kore.Simplify.Inhabitant (
    simplify,
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike (
    markSimplified,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

{- | 'simplify' simplifies a 'StringLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify ::
    Inhabitant (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify Inhabitant{inhSort} =
    OrPattern.fromTermLike $
        TermLike.markSimplified $
            mkInhabitant inhSort
