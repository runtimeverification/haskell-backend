{-|
Module      : Kore.Step.Simplification.And
Description : Tools for And pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.And
    ( makeEvaluate
    , simplify
    , simplifyEvaluated
    , simplifyEvaluatedMultiple
    , And (..)
    ) where

import Control.Applicative
    ( Alternative (empty)
    )
import Control.Monad
    ( foldM
    )
import Data.Bifunctor
    ( bimap
    )
import Data.Either
    ( partitionEithers
    )
import Data.List
    ( foldl1'
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import GHC.Stack
    ( HasCallStack
    )

import Branch
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( And (..)
    , pattern And_
    , InternalVariable
    , pattern Not_
    , Sort
    , TermLike
    , mkAnd
    , mkBottom
    , mkNot
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Simplification.AndTerms as AndTerms
    ( termAnd
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Substitution as Substitution

{-|'simplify' simplifies an 'And' of 'OrPattern'.

To do that, it first distributes the terms, making it an Or of And patterns,
each And having 'Pattern's as children, then it simplifies each of
those.

Since an Pattern is of the form term /\ predicate /\ substitution,
making an and between two Patterns roughly means and-ing each of their
components separately.

This means that a bottom component anywhere makes the result bottom, while
top can always be ignored.

When we 'and' two terms:
by Proposition 5.24 from (1),
    x and functional-pattern = functional-pattern and [x=phi]
We can generalize that to:
    x and function-pattern
        = function-pattern and ceil(function-pattern) and [x=phi]
        but note that ceil(function-pattern) is not actually needed.
We can still generalize that to:
    function-like-pattern1 and function-like-pattern2
        = function-pattern1 and function-pattern1 == function-pattern2
Also, we have
    constructor1(s1, ..., sk) and constructor2(t1, ..., tk):
        if constructor1 != constructor2 then this is bottom
        else it is
            constructor1(s1 and t1, ..., sk and tk)
    * constructor - 'inj' (sort injection) pairs become bottom
    * injection-injection pairs with the same injection work the same as
      identical constructors
    domain-value1 and domain-value1, where both are string-based:
        domain-value1 if they are equal
        bottom otherwise
    the same for two string literals and two chars
-}
simplify
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => And Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify And { andFirst = first, andSecond = second } =
    simplifyEvaluated first second

{-| simplifies an And given its two 'OrPattern' children.

See 'simplify' for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (And Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of two 'OrPattern' arguments. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually
cache information besides the pattern sort, which will make it even more useful
to carry around.

-}
simplifyEvaluated
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => OrPattern variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated first second
  | OrPattern.isFalse first  = return OrPattern.bottom
  | OrPattern.isFalse second = return OrPattern.bottom
  | OrPattern.isTrue first   = return second
  | OrPattern.isTrue second  = return first
  | otherwise                = do
    result <-
        gather $ do
            first1 <- scatter first
            second1 <- scatter second
            makeEvaluate first1 second1
    return (OrPattern.fromPatterns result)

simplifyEvaluatedMultiple
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => [OrPattern variable]
    -> simplifier (OrPattern variable)
simplifyEvaluatedMultiple [] = return OrPattern.top
simplifyEvaluatedMultiple (pat : patterns) =
    foldM simplifyEvaluated pat patterns

{-|'makeEvaluate' simplifies an 'And' of 'Pattern's.

See the comment for 'simplify' to find more details.
-}
makeEvaluate
    ::  ( SimplifierVariable variable
        , HasCallStack
        , MonadSimplify simplifier
        )
    => Pattern variable
    -> Pattern variable
    -> BranchT simplifier (Pattern variable)
makeEvaluate first second
  | Pattern.isBottom first || Pattern.isBottom second = empty
  | Pattern.isTop first = return second
  | Pattern.isTop second = return first
  | otherwise = makeEvaluateNonBool first second

makeEvaluateNonBool
    ::  ( SimplifierVariable variable
        , HasCallStack
        , MonadSimplify simplifier
        )
    => Pattern variable
    -> Pattern variable
    -> BranchT simplifier (Pattern variable)
makeEvaluateNonBool
    first@Conditional { term = firstTerm }
    second@Conditional { term = secondTerm }
  = do
    terms <- AndTerms.termAnd firstTerm secondTerm
    let firstCondition = Conditional.withoutTerm first
        secondCondition = Conditional.withoutTerm second
        initialConditions = firstCondition <> secondCondition
        merged = Conditional.andCondition terms initialConditions
    normalized <- Substitution.normalize merged
    return
        normalized
            { term =
                applyAndIdempotenceAndFindContradictions
                    (Conditional.term normalized)
            , predicate =
                applyAndIdempotenceAndFindContradictions
                    <$> Conditional.predicate normalized
            }

applyAndIdempotenceAndFindContradictions
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
applyAndIdempotenceAndFindContradictions patt =
    if noContradictions
        then foldl1' mkAndSimplified . Set.toList $ Set.union terms negatedTerms
        else mkBottom (termLikeSort patt)

  where
    (terms, negatedTerms) = splitIntoTermsAndNegations patt
    noContradictions = Set.disjoint (Set.map mkNot terms) negatedTerms
    mkAndSimplified a b
      | TermLike.isSimplified a, TermLike.isSimplified b =
        TermLike.markSimplified $ mkAnd a b
      | otherwise = mkAnd a b

splitIntoTermsAndNegations
    :: forall variable
    .  Ord variable
    => TermLike variable
    -> (Set (TermLike variable), Set (TermLike variable))
splitIntoTermsAndNegations =
    bimap Set.fromList Set.fromList
        . partitionWith termOrNegation
        . children
  where
    children :: TermLike variable -> [TermLike variable]
    children (And_ _ p1 p2) = children p1 ++ children p2
    children p = [p]

    -- Left is for regular terms, Right is negated terms
    termOrNegation
        :: TermLike variable
        -> Either (TermLike variable) (TermLike variable)
    termOrNegation t@(Not_ _ _) = Right t
    termOrNegation t            = Left t

partitionWith :: (a -> Either b c) -> [a] -> ([b], [c])
partitionWith f = partitionEithers . fmap f
