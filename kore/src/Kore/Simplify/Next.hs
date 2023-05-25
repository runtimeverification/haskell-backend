{- |
Module      : Kore.Simplify.Next
Description : Tools for Next pattern simplification.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.Next (
    simplify,
) where

import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

-- TODO: Move Next up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.

{- | 'simplify' simplifies a 'Next' pattern with an 'OrPattern'
child.

Right now this does not do any actual simplification.
-}
simplify ::
    Next Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify Next{nextChild = child} = simplifyEvaluated child

simplifyEvaluated ::
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName
simplifyEvaluated = MultiOr.map (Pattern.markSimplified . fmap mkNext)
