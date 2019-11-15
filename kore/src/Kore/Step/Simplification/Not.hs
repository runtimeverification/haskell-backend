{-|
Module      : Kore.Step.Simplification.Not
Description : Tools for Not pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Not
    ( makeEvaluate
    , simplify
    , simplifyEvaluated
    ) where

import qualified Data.Foldable as Foldable

import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.MultiOr
    ( MultiOr (..)
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeNotPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
    ( markSimplified
    )
import Kore.Step.Simplification.Simplify
import Kore.TopBottom
    ( TopBottom
    )

{-|'simplify' simplifies a 'Not' pattern with an 'OrPattern'
child.

Right now this uses the following:

* not top = bottom
* not bottom = top

-}
simplify
    :: SimplifierVariable variable
    => Not Sort (OrPattern variable)
    -> Pattern variable
simplify Not { notChild } = Pattern.fromTermLike (simplifyEvaluated notChild)

{-|'simplifyEvaluated' simplifies a 'Not' pattern given its
'OrPattern' child.

See 'simplify' for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Not Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of an 'OrPattern' argument. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually
cache information besides the pattern sort, which will make it even more useful
to carry around.

-}
simplifyEvaluated
    :: SimplifierVariable variable
    => OrPattern variable
    -> TermLike variable
simplifyEvaluated simplified =
    MultiAnd.toTermLike
    $ makeEvaluateNot
    <$> distributeNot Not { notChild = simplified, notSort = () }

{-|'makeEvaluate' simplifies a 'Not' pattern given its 'Pattern'
child.

See 'simplify' for details.
-}
makeEvaluate
    :: InternalVariable variable
    => Pattern variable
    -> TermLike variable
makeEvaluate = makeEvaluateNot . Not ()

makeEvaluateNot
    :: InternalVariable variable
    => Not sort (Pattern variable)
    -> TermLike variable
makeEvaluateNot Not { notChild } =
    mkOr
        (TermLike.markSimplified $ makeTermNot term)
        (Pattern.toTermLike $ Pattern.fromConditionSorted
            (termLikeSort term)
            (makeEvaluatePredicate predicate)
        )
  where
    (term, predicate) = Conditional.splitTerm notChild

{- | Given a not's @Internal.Condition@ argument, simplifies the @not@.

Right now there is no actual simplification, this function just creates
a negated @Internal.Condition@.

I.e. if we want to simplify @not (predicate and substitution)@, we may pass
@predicate and substitution@ to this function, which will convert
@predicate and substitution@ into a @Kore.Internal.Predicate@ and will apply
a @not@ on top of that.
-}
makeEvaluatePredicate
    :: InternalVariable variable
    => Condition variable
    -> Condition variable
makeEvaluatePredicate
    Conditional
        { term = ()
        , predicate
        , substitution
        }
  = Conditional
        { term = ()
        , predicate =
            Predicate.markSimplified
            $ makeNotPredicate
            $ makeAndPredicate predicate
            $ Predicate.fromSubstitution substitution
        , substitution = mempty
        }

makeTermNot
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
-- TODO: maybe other simplifications like
-- not ceil = floor not
-- not forall = exists not
makeTermNot (Not_ _ term) = term
makeTermNot (And_ _ term1 term2) =
    mkOr (makeTermNot term1) (makeTermNot term2)
makeTermNot term
  | isBottom term = mkTop_
  | isTop term    = mkBottom_
  | otherwise     = mkNot term

{- | Distribute 'Not' over 'MultiOr' using de Morgan's identity.
 -}
distributeNot
    :: (Ord sort, Ord child, TopBottom child)
    => Not sort (MultiOr child)
    -> MultiAnd (Not sort child)
distributeNot notOr@Not { notChild } =
    MultiAnd.make $ worker <$> Foldable.toList notChild
  where
    worker child = notOr { notChild = child }
