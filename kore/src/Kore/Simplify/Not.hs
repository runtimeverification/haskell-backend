{- |
Module      : Kore.Simplify.Not
Description : Tools for Not pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.Not (
    makeEvaluate,
    makeEvaluatePredicate,
    simplify,
    simplifyEvaluated,
    simplifyEvaluatedPredicate,
    notSimplifier,
) where

import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.MultiOr (
    MultiOr,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeNotPredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike (
    markSimplified,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.And as And
import Kore.Simplify.NotSimplifier
import Kore.Simplify.Simplify
import Kore.TopBottom (
    TopBottom (..),
 )
import Logic
import Prelude.Kore

{- |'simplify' simplifies a 'Not' pattern with an 'OrPattern'
child.

Right now this uses the following:

* not top = bottom
* not bottom = top
-}
simplify ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Not Sort (OrPattern RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
simplify sideCondition Not{notChild} =
    simplifyEvaluated sideCondition notChild

{- |'simplifyEvaluated' simplifies a 'Not' pattern given its
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
simplifyEvaluated ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyEvaluated sideCondition simplified =
    OrPattern.observeAllT $ do
        let not' = Not{notChild = simplified, notSort = ()}
        andPattern <-
            scatterAnd (MultiAnd.map makeEvaluateNot (distributeNot not'))
        mkMultiAndPattern sideCondition andPattern

simplifyEvaluatedPredicate ::
    MonadSimplify simplifier =>
    OrCondition RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
simplifyEvaluatedPredicate notChild =
    OrCondition.observeAllT $ do
        let not' = Not{notChild = notChild, notSort = ()}
        andPredicate <-
            scatterAnd
                ( MultiAnd.map
                    makeEvaluateNotPredicate
                    (distributeNot not')
                )
        mkMultiAndPredicate andPredicate

{- |'makeEvaluate' simplifies a 'Not' pattern given its 'Pattern'
child.

See 'simplify' for details.
-}
makeEvaluate ::
    Pattern RewritingVariableName ->
    OrPattern RewritingVariableName
makeEvaluate = makeEvaluateNot . Not ()

makeEvaluateNot ::
    Not sort (Pattern RewritingVariableName) ->
    OrPattern RewritingVariableName
makeEvaluateNot Not{notChild} =
    MultiOr.merge
        (MultiOr.map Pattern.fromTermLike $ makeTermNot term)
        ( makeEvaluatePredicate condition
            & Pattern.fromCondition (termLikeSort term)
            & MultiOr.singleton
        )
  where
    (term, condition) = Conditional.splitTerm notChild

{- | Given a not's @Internal.Condition@ argument, simplifies the @not@.

Right now there is no actual simplification, this function just creates
a negated @Internal.Condition@.

I.e. if we want to simplify @not (predicate and substitution)@, we may pass
@predicate and substitution@ to this function, which will convert
@predicate and substitution@ into a @Kore.Internal.Predicate@ and will apply
a @not@ on top of that.
-}
makeEvaluatePredicate ::
    Condition RewritingVariableName ->
    Condition RewritingVariableName
makeEvaluatePredicate
    Conditional
        { term = ()
        , predicate
        , substitution
        } =
        Conditional
            { term = ()
            , predicate =
                Predicate.markSimplified $
                    makeNotPredicate $
                        makeAndPredicate predicate $
                            Substitution.toPredicate substitution
            , substitution = mempty
            }

makeEvaluateNotPredicate ::
    Not sort (Condition RewritingVariableName) ->
    OrCondition RewritingVariableName
makeEvaluateNotPredicate Not{notChild = predicate} =
    OrCondition.fromConditions [makeEvaluatePredicate predicate]

makeTermNot ::
    TermLike RewritingVariableName ->
    MultiOr (TermLike RewritingVariableName)
-- TODO: maybe other simplifications like
-- not ceil = floor not
-- not forall = exists not
makeTermNot (Not_ _ term) = MultiOr.singleton term
makeTermNot (And_ _ term1 term2) =
    MultiOr.merge (makeTermNot term1) (makeTermNot term2)
makeTermNot term
    | isBottom term = MultiOr.singleton mkTop_
    | isTop term = MultiOr.singleton mkBottom_
    | otherwise = MultiOr.singleton $ TermLike.markSimplified $ mkNot term

-- | Distribute 'Not' over 'MultiOr' using de Morgan's identity.
distributeNot ::
    (Ord sort, Ord child, TopBottom child) =>
    Not sort (MultiOr child) ->
    MultiAnd (Not sort child)
distributeNot notOr@Not{notChild} =
    MultiAnd.make $ worker <$> toList notChild
  where
    worker child = notOr{notChild = child}

-- | Distribute 'MultiAnd' over 'MultiOr' and 'scatter' into 'LogicT'.
scatterAnd ::
    Ord child =>
    TopBottom child =>
    MultiAnd (MultiOr child) ->
    LogicT m (MultiAnd child)
scatterAnd = scatter . MultiAnd.distributeAnd

-- | Conjoin and simplify a 'MultiAnd' of 'Pattern'.
mkMultiAndPattern ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    MultiAnd (Pattern RewritingVariableName) ->
    LogicT simplifier (Pattern RewritingVariableName)
mkMultiAndPattern = And.makeEvaluate notSimplifier

-- | Conjoin and simplify a 'MultiAnd' of 'Condition'.
mkMultiAndPredicate ::
    MultiAnd (Condition RewritingVariableName) ->
    LogicT simplifier (Condition RewritingVariableName)
mkMultiAndPredicate predicates =
    -- Using fold because the Monoid instance of Condition
    -- implements And semantics.
    return $ fold predicates

notSimplifier ::
    MonadSimplify simplifier =>
    NotSimplifier simplifier
notSimplifier =
    NotSimplifier simplifyEvaluated
