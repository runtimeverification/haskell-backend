{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.Nu (
    simplify,
    makeEvaluate,
) where

import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern (
    fromTermLike,
    simplifiedAttribute,
    toTermLike,
 )
import Kore.Internal.TermLike (
    Nu (Nu),
    SetVariable,
    mkNu,
 )
import qualified Kore.Internal.TermLike as TermLike (
    setSimplified,
 )
import qualified Kore.Internal.TermLike as TermLike.DoNotUse
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

{- |'simplify' simplifies a 'Nu' pattern with an 'OrPattern'
child.
-}
simplify ::
    Nu RewritingVariableName (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify Nu{nuVariable, nuChild} = MultiOr.map (makeEvaluate nuVariable) nuChild

{- | evaluates a 'Nu' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate ::
    SetVariable RewritingVariableName ->
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName
makeEvaluate variable patt =
    Pattern.fromTermLike $
        TermLike.setSimplified (Pattern.simplifiedAttribute patt) $
            mkNu variable $
                Pattern.toTermLike patt
