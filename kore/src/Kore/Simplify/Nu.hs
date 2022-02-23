{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.Nu (
    simplify,
    makeEvaluate,
) where

import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern (
    fromTermLike,
    simplifiedAttribute,
    toTermLike,
 )
import Kore.Internal.TermLike (
    Nu (Nu),
    SetVariable,
    mkNu,
 )
import Kore.Internal.TermLike qualified as TermLike (
    setSimplified,
 )
import Kore.Internal.TermLike qualified as TermLike.DoNotUse
import Kore.Rewrite.RewritingVariable (
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
