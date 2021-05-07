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
import Kore.Internal.Pattern as Pattern
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
        , rewritesSort = sort
        } =
        simplifyEvaluatedRewrites sort first second

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
    Sort ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName ->
    OrPattern RewritingVariableName
simplifyEvaluatedRewrites sort first second =
    makeEvaluateRewrites
        (OrPattern.toPattern sort first)
        (OrPattern.toPattern sort second)

makeEvaluateRewrites ::
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluateRewrites first second =
    mkRewrites
        (Pattern.toTermLike first)
        (Pattern.toTermLike second)
        & TermLike.markSimplified
        & OrPattern.fromTermLike
