{-|
Module      : Kore.Step.Simplification.Iff
Description : Tools for Iff pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Iff
    ( makeEvaluate
    , simplify
    ) where

import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( mkIff
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
    )
import Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromOrPattern
    , fromPattern
    , fromPredicate
    , fromTermLike
    )
import qualified Kore.Step.Simplification.Simplifiable as Unsimplified
    ( mkNot
    )
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Iff
    ( Iff (Iff)
    )
import qualified Kore.Syntax.Iff as Iff.DoNotUse

{-|'simplify' simplifies an 'Iff' pattern with 'OrPattern'
children.

Right now this has special cases only for top and bottom children
and for children with top terms.
-}
simplify
    :: (SimplifierVariable variable)
    => Iff Sort (OrPattern variable)
    -> Simplifiable variable
simplify Iff { iffFirst = first, iffSecond = second } =
    simplifyEvaluated first second

{-| evaluates an 'Iff' given its two 'OrPattern' children.

See 'simplify' for detailed documentation.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Iff Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluated
    :: (SimplifierVariable variable)
    => OrPattern variable
    -> OrPattern variable
    -> Simplifiable variable
simplifyEvaluated
    first
    second
  | OrPattern.isTrue first   = Simplifiable.fromOrPattern second
  | OrPattern.isFalse first  =
    Unsimplified.mkNot (Simplifiable.fromOrPattern second)
  | OrPattern.isTrue second  = Simplifiable.fromOrPattern first
  | OrPattern.isFalse second =
    Unsimplified.mkNot (Simplifiable.fromOrPattern first)
  | otherwise =
    case ( firstPatterns, secondPatterns ) of
        ([firstP], [secondP]) -> makeEvaluate firstP secondP
        _ ->
            makeEvaluate
                (OrPattern.toPattern first)
                (OrPattern.toPattern second)
  where
    firstPatterns = MultiOr.extractPatterns first
    secondPatterns = MultiOr.extractPatterns second

{-| evaluates an 'Iff' given its two 'Pattern' children.

See 'simplify' for detailed documentation.
-}
makeEvaluate
    :: InternalVariable variable
    => Pattern variable
    -> Pattern variable
    -> Simplifiable variable
makeEvaluate first second
  | Pattern.isTop first = Simplifiable.fromPattern second
  | Pattern.isBottom first =
    Unsimplified.mkNot (Simplifiable.fromPattern second)
  | Pattern.isTop second = Simplifiable.fromPattern first
  | Pattern.isBottom second =
    Unsimplified.mkNot (Simplifiable.fromPattern first)
  | otherwise = makeEvaluateNonBoolIff first second

makeEvaluateNonBoolIff
    :: InternalVariable variable
    => Pattern variable
    -> Pattern variable
    -> Simplifiable variable
makeEvaluateNonBoolIff
    patt1@Conditional
        { term = firstTerm
        , predicate = firstPredicate
        , substitution = firstSubstitution
        }
    patt2@Conditional
        { term = secondTerm
        , predicate = secondPredicate
        , substitution = secondSubstitution
        }
  | isTop firstTerm, isTop secondTerm
  =
    Simplifiable.fromPredicate
    $ Predicate.markSimplified
    $ Predicate.makeIffPredicate
        (Predicate.makeAndPredicate
            firstPredicate
            (Predicate.fromSubstitution firstSubstitution)
        )
        (Predicate.makeAndPredicate
            secondPredicate
            (Predicate.fromSubstitution secondSubstitution)
        )
  | otherwise =
    Simplifiable.fromTermLike
    $ TermLike.markSimplified
    $ mkIff
        (Pattern.toTermLike patt1)
        (Pattern.toTermLike patt2)
