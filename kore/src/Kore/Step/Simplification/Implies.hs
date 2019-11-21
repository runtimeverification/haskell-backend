{-|
Module      : Kore.Step.Simplification.Implies
Description : Tools for Implies pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Implies
    ( simplify
    , simplifyEvaluated
    ) where

import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( make
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( isBottom
    , isTop
    , toTermLike
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( mkImplies
    )
import qualified Kore.Internal.TermLike as TermLike
    ( markSimplified
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Sort
    ( Sort
    )
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    , SimplifiedChildren (SimplifiedChildren)
    )
import qualified Kore.Step.Simplification.Simplifiable as Unsimplified
    ( mkNot
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromMultiAnd
    , fromMultiOr
    , fromOrPattern
    , fromPattern
    , fromPredicate
    , fromTermLike
    , top
    )
import Kore.Step.Simplification.Simplify
    ( SimplifierVariable
    )
import Kore.Syntax.Implies
    ( Implies (Implies)
    )
import qualified Kore.Syntax.Implies as Implies.DoNotUse
import Kore.TopBottom
    ( TopBottom (..)
    )

{-|'simplify' simplifies an 'Implies' pattern with 'OrPattern'
children.

Right now this uses the following simplifications:

* a -> (b or c) = (a -> b) or (a -> c)
* bottom -> b = top
* top -> b = b
* a -> top = top
* a -> bottom = not a

and it has a special case for children with top terms.
-}
simplify
    :: SimplifierVariable variable
    => Implies Sort (SimplifiedChildren variable)
    -> Simplifiable variable
simplify Implies { impliesFirst = first, impliesSecond = second } =
    simplifyEvaluated first second

{-| simplifies an Implies given its two 'OrPattern' children.

See 'simplify' for details.
-}
-- TODO: Maybe transform this to (not a) \/ b
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Implies Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluated
    :: SimplifierVariable variable
    => SimplifiedChildren variable
    -> SimplifiedChildren variable
    -> Simplifiable variable
simplifyEvaluated (SimplifiedChildren first) (SimplifiedChildren second)
  | OrPattern.isTrue first   = Simplifiable.fromOrPattern second
  | OrPattern.isFalse first  = Simplifiable.top
  | OrPattern.isTrue second  = Simplifiable.top
  | OrPattern.isFalse second =
    Unsimplified.mkNot (Simplifiable.fromOrPattern first)
  | otherwise =
    Simplifiable.fromMultiOr
        (fmap (simplifyEvaluateHalfImplies first) second)

simplifyEvaluateHalfImplies
    :: SimplifierVariable variable
    => OrPattern variable
    -> Pattern variable
    -> Simplifiable variable
simplifyEvaluateHalfImplies
    first
    second
  | OrPattern.isTrue first  = Simplifiable.fromPattern second
  | OrPattern.isFalse first = Simplifiable.top
  | Pattern.isTop second    = Simplifiable.top
  | Pattern.isBottom second =
    Unsimplified.mkNot (Simplifiable.fromOrPattern first)
  | otherwise =
    case MultiOr.extractPatterns first of
        [firstP] -> makeEvaluateImplies firstP second
        firstPatterns -> distributeEvaluateImplies firstPatterns second

distributeEvaluateImplies
    :: SimplifierVariable variable
    => [Pattern variable]
    -> Pattern variable
    -> Simplifiable variable
distributeEvaluateImplies firsts second =
    Simplifiable.fromMultiAnd
    $ MultiAnd.make
    $ map (`makeEvaluateImplies` second) firsts

makeEvaluateImplies
    :: InternalVariable variable
    => Pattern variable
    -> Pattern variable
    -> Simplifiable variable
makeEvaluateImplies
    first second
  | Pattern.isTop first =
    Simplifiable.fromPattern second
  | Pattern.isBottom first =
    Simplifiable.top
  | Pattern.isTop second =
    Simplifiable.top
  | Pattern.isBottom second =
    Unsimplified.mkNot (Simplifiable.fromPattern first)
  | otherwise =
    makeEvaluateImpliesNonBool first second

makeEvaluateImpliesNonBool
    :: InternalVariable variable
    => Pattern variable
    -> Pattern variable
    -> Simplifiable variable
makeEvaluateImpliesNonBool
    pattern1@Conditional
        { term = firstTerm
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    pattern2@Conditional
        { term = secondTerm
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  | isTop firstTerm, isTop secondTerm =
    Simplifiable.fromPredicate
    $ Predicate.markSimplified
    $ Predicate.makeImpliesPredicate
        (Predicate.makeAndPredicate
            firstPredicate
            (Predicate.fromSubstitution firstSubstitution)
        )
        (Predicate.makeAndPredicate
            secondPredicate
            (Predicate.fromSubstitution secondSubstitution)
        )
  | otherwise =
    -- TODO (thomas.tuegel): Maybe this should be an error?
    Simplifiable.fromTermLike
    $ TermLike.markSimplified
    $ mkImplies
        (Pattern.toTermLike pattern1)
        (Pattern.toTermLike pattern2)
