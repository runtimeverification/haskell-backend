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
    , simplifyEvaluatedPredicate
    ) where

import qualified Data.Foldable as Foldable

import Branch
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.MultiOr
    ( MultiOr
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import qualified Kore.Internal.OrPredicate as OrPredicate
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike hiding
    ( mkAnd
    )
import qualified Kore.Internal.TermLike as TermLike
    ( markSimplified
    )
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeNotPredicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Step.Simplification.And as And
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

simplifyEvaluatedPredicate
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => OrPredicate variable
    -> simplifier (OrPredicate variable)
simplifyEvaluatedPredicate notChild =
    fmap OrPredicate.fromPredicates $ gather $ do
        let not' = Not { notChild = notChild, notSort = () }
        andPredicate <- scatterAnd (makeEvaluateNotPredicate <$> distributeNot not')
        mkMultiAndPredicate andPredicate

{-|'makeEvaluate' simplifies a 'Not' pattern given its 'Pattern'
child.

See 'simplify' for details.
-}
makeEvaluate
    :: InternalVariable variable
    => Pattern variable
    -> OrPattern variable
makeEvaluate = makeEvaluateNot . Not ()

makeEvaluateNot
    :: InternalVariable variable
    => Not sort (Pattern variable)
    -> OrPattern variable
makeEvaluateNot Not { notChild } =
    OrPattern.fromPatterns
        [ Pattern.fromTermLike $ TermLike.markSimplified $ makeTermNot term
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
    :: InternalVariable variable
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
            Syntax.Predicate.markSimplified
            $ makeNotPredicate
            $ makeAndPredicate predicate
            $ Syntax.Predicate.fromSubstitution substitution
        , substitution = mempty
        }

makeEvaluateNotPredicate
    :: InternalVariable variable
    => Not sort (Predicate variable)
    -> OrPredicate variable
makeEvaluateNotPredicate Not { notChild = predicate } =
    OrPredicate.fromPredicates [ makeEvaluatePredicate predicate ]

makeTermNot
    :: InternalVariable variable
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
    :: (Ord sort, Ord child, TopBottom child)
    => Not sort (MultiOr child)
    -> MultiAnd (Not sort child)
distributeNot notOr@Not { notChild } =
    MultiAnd.make $ worker <$> Foldable.toList notChild
  where
    worker child = notOr { notChild = child }

{- | Distribute 'MultiAnd' over 'MultiOr'.
 -}
distributeAnd
    :: MultiAnd (MultiOr child)
    -> MultiOr (MultiAnd child)
distributeAnd = sequenceA

{- | Distribute 'MultiAnd' over 'MultiOr' and 'scatter' into 'BranchT'.
 -}
scatterAnd
    :: Monad m
    => MultiAnd (MultiOr child)
    -> BranchT m (MultiAnd child)
scatterAnd = scatter . distributeAnd

{- | Conjoin and simplify a 'MultiAnd' of 'Pattern'.
 -}
mkMultiAndPattern
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => MultiAnd (Pattern variable)
    -> BranchT simplifier (Pattern variable)
mkMultiAndPattern patterns =
    Foldable.foldrM And.makeEvaluate Pattern.top patterns

{- | Conjoin and simplify a 'MultiAnd' of 'Predicate'.
 -}
mkMultiAndPredicate
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => MultiAnd (Predicate variable)
    -> BranchT simplifier (Predicate variable)
mkMultiAndPredicate predicates =
    -- Using Foldable.fold because the Monoid instance of Predicate
    -- implements And semantics.
    return $ Foldable.fold predicates
