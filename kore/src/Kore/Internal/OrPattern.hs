{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Internal.OrPattern (
    OrPattern,
    coerceSort,
    markSimplified,
    isSimplified,
    hasSimplifiedChildren,
    hasSimplifiedChildrenIgnoreConditions,
    forgetSimplified,
    fromPatterns,
    toPatterns,
    fromPattern,
    fromOrCondition,
    fromTermLike,
    bottom,
    isFalse,
    isPredicate,
    getSortIfNotBottom,
    topOf,
    isTrue,
    toPattern,
    toTermLike,
    targetBinder,
    mapVariables,
    MultiOr.flatten,
    MultiOr.gather,
    MultiOr.observeAllT,
    MultiOr.map,
    MultiOr.traverse,
    MultiOr.traverseOr,
) where

import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Condition qualified as Condition (
    fromPredicate,
    toPredicate,
 )
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.MultiOr (
    MultiOr,
 )
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition.SideCondition qualified as SideCondition (
    Representation,
 )
import Kore.Internal.TermLike (
    InternalVariable,
    Sort,
    TermLike,
    mkBottom,
    mkOr,
 )
import Kore.Syntax.Variable
import Kore.TopBottom (
    TopBottom (..),
 )
import Kore.Variables.Binding (
    Binder (..),
 )
import Kore.Variables.Target (
    Target (..),
    mkElementTarget,
    targetIfEqual,
 )
import Logic qualified
import Prelude.Kore

-- | The disjunction of 'Pattern'.
type OrPattern variable = MultiOr (Pattern variable)

markSimplified ::
    InternalVariable variable =>
    OrPattern variable ->
    OrPattern variable
markSimplified = MultiOr.map Pattern.markSimplified

isSimplified :: SideCondition.Representation -> OrPattern variable -> Bool
isSimplified sideCondition = all (Pattern.isSimplified sideCondition)

{- | Checks whether all patterns in the disjunction have simplified children.

See also: 'Pattern.hasSimplifiedChildren'
-}
hasSimplifiedChildren ::
    InternalVariable variable =>
    SideCondition.Representation ->
    OrPattern variable ->
    Bool
hasSimplifiedChildren sideCondition =
    all (Pattern.hasSimplifiedChildren sideCondition)

{- | Checks whether all patterns in the disjunction have simplified children,
ignoring the conditions used to simplify them.

See also: 'Pattern.hasSimplifiedChildrenIgnoreConditions'
-}
hasSimplifiedChildrenIgnoreConditions ::
    InternalVariable variable =>
    OrPattern variable ->
    Bool
hasSimplifiedChildrenIgnoreConditions =
    all Pattern.hasSimplifiedChildrenIgnoreConditions

forgetSimplified ::
    InternalVariable variable => OrPattern variable -> OrPattern variable
forgetSimplified = fromPatterns . map Pattern.forgetSimplified . toPatterns

-- | A "disjunction" of one 'Pattern.Pattern'.
fromPattern :: Pattern variable -> OrPattern variable
fromPattern = from

-- | Disjoin a collection of patterns.
fromPatterns ::
    (Foldable f, InternalVariable variable) =>
    f (Pattern variable) ->
    OrPattern variable
fromPatterns = from . toList

-- | Examine a disjunction of 'Pattern.Pattern's.
toPatterns :: OrPattern variable -> [Pattern variable]
toPatterns = from

fromOrCondition ::
    InternalVariable variable =>
    Sort ->
    OrCondition variable ->
    OrPattern variable
fromOrCondition sort conditions =
    MultiOr.observeAll $ Pattern.fromCondition sort <$> Logic.scatter conditions

{- | A "disjunction" of one 'TermLike'.

See also: 'fromPattern'
-}
fromTermLike ::
    InternalVariable variable =>
    TermLike variable ->
    OrPattern variable
fromTermLike = fromPattern . Pattern.fromTermLike

{- | @\\bottom@

@
isFalse bottom == True
@
-}
bottom :: InternalVariable variable => OrPattern variable
bottom = fromPatterns []

-- | 'isFalse' checks if the 'Or' is composed only of bottom items.
isFalse :: OrPattern variable -> Bool
isFalse = isBottom

{- | @\\top@

@
isTrue (topOf _) == True
@
-}
topOf :: InternalVariable variable => Sort -> OrPattern variable
topOf sort = fromPattern (Pattern.topOf sort)

-- | 'isTrue' checks if the 'Or' has a single top pattern.
isTrue :: OrPattern variable -> Bool
isTrue = isTop

-- | 'toPattern' transforms an 'OrPattern' into a 'Pattern.Pattern'.
toPattern ::
    forall variable.
    InternalVariable variable =>
    Sort ->
    OrPattern variable ->
    Pattern variable
toPattern sort multiOr =
    case toList multiOr of
        [] -> Pattern.bottomOf sort
        [patt] -> patt
        patts -> foldr1 mergeWithOr patts
  where
    mergeWithOr :: Pattern variable -> Pattern variable -> Pattern variable
    mergeWithOr patt1 patt2
        | isTop term1
          , isTop term2 =
            term1
                `Conditional.withCondition` mergeConditionsWithOr predicate1 predicate2
        | otherwise =
            Pattern.fromTermLike
                (mkOr (Pattern.toTermLike patt1) (Pattern.toTermLike patt2))
      where
        (term1, predicate1) = Pattern.splitTerm patt1
        (term2, predicate2) = Pattern.splitTerm patt2

    mergeConditionsWithOr ::
        Condition variable -> Condition variable -> Condition variable
    mergeConditionsWithOr predicate1 predicate2 =
        Condition.fromPredicate
            ( Predicate.makeOrPredicate
                (Condition.toPredicate predicate1)
                (Condition.toPredicate predicate2)
            )

{- Check if an OrPattern can be reduced to a Predicate. -}
isPredicate :: OrPattern variable -> Bool
isPredicate = all Pattern.isPredicate

-- | Gets the `Sort` of a non-empty 'OrPattern' and othewise returns `Nothing`.
getSortIfNotBottom :: OrPattern variable -> Maybe Sort
getSortIfNotBottom multiOr =
    case toList multiOr of
        [] -> Nothing
        p : _ -> Just (Pattern.patternSort p)

-- | Transforms a 'Pattern' into a 'TermLike'.
toTermLike ::
    InternalVariable variable =>
    Sort ->
    OrPattern variable ->
    TermLike variable
toTermLike sort multiOr =
    case toList multiOr of
        [] -> mkBottom sort
        [patt] -> Pattern.toTermLike patt
        patts -> foldr1 mkOr (Pattern.toTermLike <$> patts)

coerceSort ::
    (HasCallStack, InternalVariable variable) =>
    Sort ->
    OrPattern variable ->
    OrPattern variable
coerceSort sort =
    fromPatterns
        . map (Pattern.coerceSort sort)
        . toPatterns

targetBinder ::
    forall variable.
    InternalVariable variable =>
    Binder (ElementVariable variable) (OrPattern variable) ->
    Binder (ElementVariable (Target variable)) (OrPattern (Target variable))
targetBinder Binder{binderVariable, binderChild} =
    let newVar = mkElementTarget binderVariable
        targetBoundVariables =
            targetIfEqual $
                unElementVariableName . variableName $ binderVariable
        newChild =
            MultiOr.map
                ( Pattern.mapVariables
                    AdjSomeVariableName
                        { adjSomeVariableNameElement =
                            ElementVariableName targetBoundVariables
                        , adjSomeVariableNameSet = SetVariableName NonTarget
                        }
                )
                binderChild
     in Binder
            { binderVariable = newVar
            , binderChild = newChild
            }

mapVariables ::
    (InternalVariable variable1, InternalVariable variable2) =>
    AdjSomeVariableName (variable1 -> variable2) ->
    OrPattern variable1 ->
    OrPattern variable2
mapVariables = MultiOr.map . Pattern.mapVariables
