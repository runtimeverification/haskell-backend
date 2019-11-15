{-|
Module      : Kore.Step.Simplification.In
Description : Tools for In pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.In
    ( simplify
    ) where

import Kore.Internal.Condition as Condition
    ( fromPredicate
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeCeilPredicate
    , makeInPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
    ( markSimplified
    )
import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplify

{-|'simplify' simplifies an 'In' pattern with 'OrPattern'
children.

Right now this uses the following simplifications:

* bottom in a = bottom
* a in bottom = bottom
* top in a = ceil(a)
* a in top = ceil(a)

TODO(virgil): It does not have yet a special case for children with top terms.
-}
simplify
    :: SimplifierVariable variable
    => In Sort (OrPattern variable)
    -> Pattern variable
simplify In { inContainedChild = first, inContainingChild = second } =
    simplifyEvaluatedIn first second

{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make
'simplifyEvaluatedIn' take an argument of type

> CofreeF (In Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluateIn' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluatedIn
    :: forall variable
    .  SimplifierVariable variable
    => OrPattern variable
    -> OrPattern variable
    -> Pattern variable
simplifyEvaluatedIn first second
  | OrPattern.isFalse first  = Pattern.bottom
  | OrPattern.isFalse second = Pattern.bottom

  | OrPattern.isTrue first =
    Pattern.fromCondition
    $ Condition.fromPredicate
    $ makeCeilPredicate (OrPattern.toTermLike second)
  | OrPattern.isTrue second =
    Pattern.fromCondition
    $ Condition.fromPredicate
    $ makeCeilPredicate (OrPattern.toTermLike first)

  | otherwise =
    OrPattern.toPattern (makeEvaluateIn <$> first <*> second)

makeEvaluateIn
    :: SimplifierVariable variable
    => Pattern variable
    -> Pattern variable
    -> Pattern variable
makeEvaluateIn first second
  | Pattern.isTop first =
    Pattern.fromCondition
    $ Condition.fromPredicate
    $ makeCeilPredicate (Pattern.toTermLike second)
  | Pattern.isTop second =
    Pattern.fromCondition
    $ Condition.fromPredicate
    $ makeCeilPredicate (Pattern.toTermLike first)
  | Pattern.isBottom first || Pattern.isBottom second = Pattern.bottom
  | otherwise = makeEvaluateNonBoolIn first second

makeEvaluateNonBoolIn
    :: InternalVariable variable
    => Pattern variable
    -> Pattern variable
    -> Pattern variable
makeEvaluateNonBoolIn patt1 patt2 =
    Pattern.fromCondition
    $ Condition.fromPredicate
    $ Predicate.markSimplified
    $ makeInPredicate
        -- TODO: Wrap in 'contained' and 'container'.
        (Pattern.toTermLike patt1)
        (Pattern.toTermLike patt2)
