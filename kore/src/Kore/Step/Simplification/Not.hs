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

import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.OrPattern as OrPattern
    ( toPatterns
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
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    , SimplifiedChildren (SimplifiedChildren)
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromMultiAnd
    , fromPattern
    , fromTermLike
    , top
    )
import qualified Kore.Step.Simplification.Simplifiable as Unsimplified
    ( mkNot
    , mkOr
    )
import Kore.Step.Simplification.Simplify

{-|'simplify' simplifies a 'Not' pattern with an 'OrPattern'
child.

Right now this uses the following:

* not top = bottom
* not bottom = top

-}
simplify
    :: SimplifierVariable variable
    => Not Sort (SimplifiedChildren variable)
    -> Simplifiable variable
simplify Not { notChild } = simplifyEvaluated notChild

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
    => SimplifiedChildren variable
    -> Simplifiable variable
simplifyEvaluated (SimplifiedChildren simplified) =
    case OrPattern.toPatterns simplified of
        [] -> Simplifiable.top
        [patt] -> makeEvaluate patt
        _ -> Simplifiable.fromMultiAnd
            (distributeNot Not { notChild = simplified, notSort = () })

{-|'makeEvaluate' simplifies a 'Not' pattern given its 'Pattern'
child.

See 'simplify' for details.
-}
makeEvaluate
    :: InternalVariable variable
    => Pattern variable
    -> Simplifiable variable
makeEvaluate patt =
    Unsimplified.mkOr
        ( Simplifiable.fromTermLike
        $ TermLike.markSimplified
        $ makeTermNot term
        )
        ( Simplifiable.fromPattern
        $ Pattern.fromConditionSorted
            (termLikeSort term)
            (makeEvaluatePredicate predicate)
        )
  where
    (term, predicate) = Conditional.splitTerm patt

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
    :: InternalVariable variable
    => Not sort (OrPattern variable)
    -> MultiAnd (Simplifiable variable)
distributeNot Not { notChild } =
    MultiAnd.make $ map worker (OrPattern.toPatterns notChild)
  where
    worker child = Unsimplified.mkNot (Simplifiable.fromPattern child)
