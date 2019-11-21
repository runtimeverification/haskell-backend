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

import qualified Kore.Internal.Condition as Condition
    ( fromPredicate
    , hasFreeVariable
    , markSimplified
    , toPredicate
    )
import qualified Kore.Internal.Conditional as Conditional
    ( withCondition
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( isBottom
    , isTop
    , splitTerm
    , toTermLike
    )
import Kore.Internal.Predicate
    ( makeForallPredicate
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
import Kore.Step.Simplification.Simplifiable
    ( FullySimplified (FullySimplified)
    , Simplifiable
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( bottom
    , fromPattern
    , fromTermLike
    , onlyForOrSimplified
    , top
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
    => Forall Sort variable (FullySimplified variable)
    -> Simplifiable variable
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
    :: forall variable
    .  InternalVariable variable
    => ElementVariable variable
    -> FullySimplified variable
    -> Simplifiable variable
simplifyEvaluated variable (FullySimplified child)
  | OrPattern.isTrue child  = Simplifiable.top
  | OrPattern.isFalse child = Simplifiable.bottom
  | otherwise               = case OrPattern.toPatterns child of
    [] -> Simplifiable.bottom
    [patt] -> makeEvaluate variable patt
    patts
      | all pattHasFreeVariable patts -> Simplifiable.onlyForOrSimplified child
      | otherwise ->
        Simplifiable.fromTermLike
        $ TermLike.markSimplified
        $ mkForall variable
        $ OrPattern.toTermLike child
      where
        pattHasFreeVariable :: Pattern variable -> Bool
        pattHasFreeVariable =
            TermLike.hasFreeVariable (ElemVar variable) . Pattern.toTermLike

{-| evaluates an 'Forall' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    :: InternalVariable variable
    => ElementVariable variable
    -> Pattern variable
    -> Simplifiable variable
makeEvaluate variable patt
  | Pattern.isTop patt    = Simplifiable.top
  | Pattern.isBottom patt = Simplifiable.bottom
  | not variableInTerm && not variableInCondition =
    Simplifiable.fromPattern patt
  | predicateIsBoolean =
    Simplifiable.fromPattern
        ( TermLike.markSimplified (mkForall variable term)
        `Conditional.withCondition` predicate
        )
  | termIsBoolean =
    Simplifiable.fromPattern
        ( term
        `Conditional.withCondition` Condition.markSimplified
            (Condition.fromPredicate
                (makeForallPredicate variable (Condition.toPredicate predicate))
            )
        )
  | otherwise =
    Simplifiable.fromTermLike
    $ TermLike.markSimplified
    $ mkForall variable
    $ Pattern.toTermLike patt
  where
    (term, predicate) = Pattern.splitTerm patt
    unifiedVariable = ElemVar variable
    variableInTerm = TermLike.hasFreeVariable unifiedVariable term
    variableInCondition = Condition.hasFreeVariable unifiedVariable predicate
    termIsBoolean = isTop term || isBottom term
    predicateIsBoolean = isTop predicate || isBottom predicate
