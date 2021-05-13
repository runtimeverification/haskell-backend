{- |
Module      : Kore.Step.Simplification.Rewrites
Description : Tools for Rewrites pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Rewrites (
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
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

{- | Simplify a 'Rewrites' pattern with a 'OrPattern' child.

Right now this does not do any actual simplification.

TODO(virgil): Should I even bother to simplify Rewrites? Maybe to implies+next?
-}
simplify ::
    Rewrites Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify
    Rewrites
        { rewritesFirst = first
        , rewritesSecond = second
        } =
        simplifyEvaluatedRewrites first second

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make
'simplifyEvaluatedRewrites' take an argument of type

> CofreeF (Or Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of
'makeEvaluateRewrites' may be changed analogously. The 'Attribute.Pattern'
annotation will eventually cache information besides the pattern sort, which
will make it even more useful to carry around.

-}
simplifyEvaluatedRewrites ::
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName
simplifyEvaluatedRewrites first second =
    makeEvaluateRewrites
        first
        second

makeEvaluateRewrites ::
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluateRewrites first second =
    OrPattern.fromTermLike $
        TermLike.markSimplified $
            mkRewrites
                (OrPattern.toTermLike first)
                (OrPattern.toTermLike second)
