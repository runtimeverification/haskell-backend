{-|
Module      : Kore.Step.Simplification.Forall
Description : Tools for Forall pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Forall
    ( simplify
    , makeEvaluate
    ) where

import qualified Kore.Internal.Conditional as Conditional
    ( withCondition
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( bottom
    , fromTermLike
    , isBottom
    , isTop
    , splitTerm
    , toTermLike
    , top
    )
import qualified Kore.Internal.Predicate as Predicate
    ( fromPredicate
    , hasFreeVariable
    , markSimplified
    , toPredicate
    )
import Kore.Internal.TermLike
    ( ElementVariable
    , Forall (Forall)
    , InternalVariable
    , Sort
    , mkForall
    )
import qualified Kore.Internal.TermLike as TermLike
    ( hasFreeVariable
    , markSimplified
    )
import qualified Kore.Internal.TermLike as TermLike.DoNotUse
import Kore.Predicate.Predicate
    ( makeForallPredicate
    )
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

-- TODO: Move Forall up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies an 'Forall' pattern with an 'OrPattern'
child.

Right now this has special cases for (top and bottom children),
(top and bottom term) and (top and bottom predicate-substitution).

Note that while forall x . phi(x) and [x=alpha] can be simplified
(it's bottom if x's sort is multivalued and alpha is not the 'x' pattern or
the identity function applied to the pattern x, or phi(alpha) otherwise),
we only expect forall usage for symbolic variables, so we won't attempt to
simplify it this way.
-}
simplify
    :: InternalVariable variable
    => Forall Sort variable (OrPattern variable)
    -> OrPattern variable
simplify Forall { forallVariable, forallChild } =
    simplifyEvaluated forallVariable forallChild

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Forall Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of a 'variable' and an 'OrPattern' argument. The type of
'makeEvaluate' may be changed analogously. The 'Attribute.Pattern' annotation
will eventually cache information besides the pattern sort, which will make it
even more useful to carry around.

-}
simplifyEvaluated
    :: InternalVariable variable
    => ElementVariable variable
    -> OrPattern variable
    -> OrPattern variable
simplifyEvaluated variable simplified
  | OrPattern.isTrue simplified  = simplified
  | OrPattern.isFalse simplified = simplified
  | otherwise                    = makeEvaluate variable <$> simplified

{-| evaluates an 'Forall' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    :: InternalVariable variable
    => ElementVariable variable
    -> Pattern variable
    -> Pattern variable
makeEvaluate variable patt
  | Pattern.isTop patt    = Pattern.top
  | Pattern.isBottom patt = Pattern.bottom
  | not variableInTerm && not variableInPredicate = patt
  | predicateIsBoolean =
    TermLike.markSimplified (mkForall variable term)
    `Conditional.withCondition` predicate
  | termIsBoolean =
    term
    `Conditional.withCondition` Predicate.markSimplified
        (Predicate.fromPredicate
            (makeForallPredicate variable (Predicate.toPredicate predicate))
        )
  | otherwise =
    Pattern.fromTermLike
    $ TermLike.markSimplified
    $ mkForall variable
    $ Pattern.toTermLike patt
  where
    (term, predicate) = Pattern.splitTerm patt
    unifiedVariable = ElemVar variable
    variableInTerm = TermLike.hasFreeVariable unifiedVariable term
    variableInPredicate = Predicate.hasFreeVariable unifiedVariable predicate
    termIsBoolean = isTop term || isBottom term
    predicateIsBoolean = isTop predicate || isBottom predicate
