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
    , makeEvaluatePredicate
    , simplify
    , simplifyEvaluated
    ) where

import qualified Data.Foldable as Foldable

import qualified Kore.Internal.Conditional as Conditional
import           Kore.Internal.MultiAnd
                 ( MultiAnd )
import qualified Kore.Internal.MultiAnd as MultiAnd
import           Kore.Internal.MultiOr
                 ( MultiOr )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike hiding
                 ( mkAnd )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeNotPredicate )
import qualified Kore.Predicate.Predicate as Predicate
import qualified Kore.Step.Simplification.And as And
import           Kore.Step.Simplification.Data
import           Kore.Unparser

{-|'simplify' simplifies a 'Not' pattern with an 'OrPattern'
child.

Right now this uses the following:

* not top = bottom
* not bottom = top

-}
simplify
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Not Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
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
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated simplified =
    fmap OrPattern.fromPatterns $ gather $ do
        let not' = Not { notChild = simplified, notSort = () }
        andPattern <- scatterAnd (makeEvaluateNot <$> distributeNot not')
        mkMultiAndPattern andPattern

{-|'makeEvaluate' simplifies a 'Not' pattern given its 'Pattern'
child.

See 'simplify' for details.
-}
makeEvaluate
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => Pattern variable
    -> OrPattern variable
makeEvaluate = makeEvaluateNot . Not ()

makeEvaluateNot
    :: (Ord variable, Show variable, SortedVariable variable, Unparse variable)
    => Not sort (Pattern variable)
    -> OrPattern variable
makeEvaluateNot Not { notChild } =
    OrPattern.fromPatterns
        [ Pattern.fromTermLike $ makeTermNot term
        , Pattern.fromPredicateSorted
            (termLikeSort term)
            (makeEvaluatePredicate predicate)
        ]
  where
    (term, predicate) = Conditional.splitTerm notChild

{- | Given a not's @Internal.Predicate@ argument, simplifies the @not@.

Right now there is no actual simplification, this function just creates
a negated @Internal.Predicate@.

I.e. if we want to simplify @not (predicate and substitution)@, we may pass
@predicate and substitution@ to this function, which will convert
@predicate and substitution@ into a @Kore.Predicate.Predicate@ and will apply
a @not@ on top of that.
-}
makeEvaluatePredicate
    ::  ( Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        )
    => Predicate variable
    -> Predicate variable
makeEvaluatePredicate
    Conditional
        { term = ()
        , predicate
        , substitution
        }
  = Conditional
        { term = ()
        , predicate =
            makeNotPredicate
            $ makeAndPredicate predicate
            $ Predicate.fromSubstitution substitution
        , substitution = mempty
        }

makeTermNot
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => TermLike variable
    -> TermLike variable
-- TODO: maybe other simplifications like
-- not ceil = floor not
-- not forall = exists not
makeTermNot term
  | isBottom term = mkTop    (termLikeSort term)
  | isTop term    = mkBottom (termLikeSort term)
  | otherwise     = mkNot term

{- | Distribute 'Not' over 'MultiOr' using de Morgan's identity.
 -}
distributeNot
    :: (Ord sort, Ord variable)
    => Not sort (OrPattern variable)
    -> MultiAnd (Not sort (Pattern variable))
distributeNot notOr@Not { notChild } =
    MultiAnd.make $ worker <$> Foldable.toList notChild
  where
    worker child = notOr { notChild = child }

{- | Distribute 'MultiAnd' over 'MultiOr'.
 -}
distributeAnd
    :: MultiAnd (OrPattern variable)
    -> MultiOr (MultiAnd (Pattern variable))
distributeAnd = sequenceA

{- | Distribute 'MultiAnd' over 'MultiOr' and 'scatter' into 'BranchT'.
 -}
scatterAnd
    :: Monad m
    => MultiAnd (OrPattern variable)
    -> BranchT m (MultiAnd (Pattern variable))
scatterAnd = scatter . distributeAnd

{- | Conjoin and simplify a 'MultiAnd' of 'Pattern'.
 -}
mkMultiAndPattern
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => MultiAnd (Pattern variable)
    -> BranchT simplifier (Pattern variable)
mkMultiAndPattern patterns =
    Foldable.foldrM And.makeEvaluate Pattern.top patterns
