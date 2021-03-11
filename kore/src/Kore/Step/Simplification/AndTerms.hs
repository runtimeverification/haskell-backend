{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}

{-# LANGUAGE Strict #-}

module Kore.Step.Simplification.AndTerms
    ( termUnification
    , maybeTermAnd
    , maybeTermEquals
    , TermSimplifier
    , TermTransformationOld
    , cannotUnifyDistinctDomainValues
    , functionAnd
    , compareForEquals
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT (..)
    )
import qualified Control.Error as Error
import qualified Data.Functor.Foldable as Recursive
import Data.String
    ( fromString
    )

import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Endianness as Builtin.Endianness
import qualified Kore.Builtin.Int as Builtin.Int
import qualified Kore.Builtin.KEqual as Builtin.KEqual
import qualified Kore.Builtin.List as Builtin.List
import qualified Kore.Builtin.Map as Builtin.Map
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Builtin.Signedness as Builtin.Signedness
import qualified Kore.Builtin.String as Builtin.String
import Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrCondition as OrCondition
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( pattern PredicateTrue
    , makeEqualsPredicate
    , makeNotPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( topTODO
    )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Log.DebugUnification
    ( debugUnificationSolved
    , debugUnificationUnsolved
    , whileDebugUnification
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import qualified Kore.Step.Simplification.Exists as Exists
import Kore.Step.Simplification.ExpandAlias
    ( expandAlias
    )
import Kore.Step.Simplification.InjSimplifier
import Kore.Step.Simplification.NoConfusion
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Overloading as Overloading
import qualified Kore.Step.Simplification.SimplificationType as SimplificationType
    ( SimplificationType (..)
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Syntax.PatternF
    ( Const (..)
    )
import Kore.TopBottom
import Kore.Unification.Unify as Unify
import Kore.Unparser
import Pair
import qualified Pretty

{- | Unify two terms without discarding the terms.

We want to keep the terms because substitution relies on the result not being
@\\bottom@.

When a case is not implemented, @termUnification@ will create a @\\ceil@ of
the conjunction of the two terms.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

-}
termUnification
    :: forall unifier
    .  MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> unifier (Pattern RewritingVariableName)
termUnification notSimplifier = \term1 term2 ->
    whileDebugUnification term1 term2 $ do
        result <- termUnificationWorker term1 term2
        debugUnificationSolved result
        pure result
  where
    termUnificationWorker
        :: TermLike RewritingVariableName
        -> TermLike RewritingVariableName
        -> unifier (Pattern RewritingVariableName)
    termUnificationWorker pat1 pat2 = do
        let
            maybeTermUnification
                :: MaybeT unifier (Pattern RewritingVariableName)
            maybeTermUnification =
                maybeTermAnd notSimplifier termUnificationWorker pat1 pat2
        Error.maybeT
            (incompleteUnificationPattern pat1 pat2)
            pure
            maybeTermUnification

    incompleteUnificationPattern term1 term2 = do
        debugUnificationUnsolved term1 term2
        mkAnd term1 term2
            & Pattern.fromTermLike
            & return

maybeTermEquals
    :: MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> TermSimplifier RewritingVariableName unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
maybeTermEquals notSimplifier childTransformers first second = asum
    [ Builtin.Int.unifyInt first second
    , Builtin.Bool.unifyBool first second
    , Builtin.String.unifyString first second
    , unifyDomainValue first second
    , unifyStringLiteral first second
    , equalAndEquals first second
    , bytesDifferent first second
    , bottomTermEquals SideCondition.topTODO first second
    , termBottomEquals SideCondition.topTODO first second
    , variableFunctionEquals first second
    , variableFunctionEquals second first
    , equalInjectiveHeadsAndEquals childTransformers first second
    , sortInjectionAndEquals childTransformers first second
    , constructorSortInjectionAndEquals first second
    , constructorAndEqualsAssumesDifferentHeads first second
    , overloadedConstructorSortInjectionAndEquals
        childTransformers
        first
        second
    , Builtin.Bool.unifyBoolAnd childTransformers first second
    , Builtin.Bool.unifyBoolOr childTransformers first second
    , Builtin.Bool.unifyBoolNot childTransformers first second
    , Builtin.Int.unifyIntEq childTransformers notSimplifier first second
    , Builtin.String.unifyStringEq
        childTransformers
        notSimplifier
        first
        second
    , Builtin.KEqual.unifyKequalsEq
        childTransformers
        notSimplifier
        first
        second
    , Builtin.Endianness.unifyEquals first second
    , Builtin.Signedness.unifyEquals first second
    , Builtin.Map.unifyEquals childTransformers first second
    , Builtin.Map.unifyNotInKeys childTransformers notSimplifier first second
    , Builtin.Set.unifyEquals childTransformers first second
    , Builtin.List.unifyEquals
        SimplificationType.Equals
        childTransformers
        first
        second
    , domainValueAndConstructorErrors first second
    ]

maybeTermAnd
    :: MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> TermSimplifier RewritingVariableName unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
maybeTermAnd notSimplifier childTransformers first second = asum
    [ expandAlias
        (maybeTermAnd notSimplifier childTransformers)
        first
        second
    , boolAnd first second
    , Builtin.Int.unifyInt first second
    , Builtin.Bool.unifyBool first second
    , Builtin.String.unifyString first second
    , unifyDomainValue first second
    , unifyStringLiteral first second
    , equalAndEquals first second
    , bytesDifferent first second
    , variableFunctionAnd first second
    , variableFunctionAnd second first
    , equalInjectiveHeadsAndEquals childTransformers first second
    , sortInjectionAndEquals childTransformers first second
    , constructorSortInjectionAndEquals first second
    , constructorAndEqualsAssumesDifferentHeads first second
    , overloadedConstructorSortInjectionAndEquals
        childTransformers
        first
        second
    , Builtin.Bool.unifyBoolAnd childTransformers first second
    , Builtin.Bool.unifyBoolOr childTransformers first second
    , Builtin.Bool.unifyBoolNot childTransformers first second
    , Builtin.KEqual.unifyKequalsEq
        childTransformers
        notSimplifier
        first
        second
    , Builtin.KEqual.unifyIfThenElse childTransformers first second
    , Builtin.Endianness.unifyEquals first second
    , Builtin.Signedness.unifyEquals first second
    , Builtin.Map.unifyEquals childTransformers first second
    , Builtin.Set.unifyEquals childTransformers first second
    , Builtin.List.unifyEquals
        SimplificationType.And
        childTransformers
        first
        second
    , domainValueAndConstructorErrors first second
    , Error.hoistMaybe (functionAnd first second)
    ]

{- | Construct the conjunction or unification of two terms.

Each @TermTransformationOld@ should represent one unification case and each
unification case should be handled by only one @TermTransformationOld@. If the
pattern heads do not match the case under consideration, call 'empty' to allow
another case to handle the patterns. If the pattern heads do match the
unification case, then use 'lift' to wrap the implementation
of that case.

All the @TermTransformationOld@s and similar functions defined in this module
call 'empty' unless given patterns matching their unification case.
-}

type TermTransformationOld variable unifier =
       TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)

-- | Simplify the conjunction of terms where one is a predicate.
boolAnd
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
boolAnd first second
  | isBottom first  = do
      explainBoolAndBottom first second
      return (Pattern.fromTermLike first)
  | isTop first     = return (Pattern.fromTermLike second)
  | isBottom second = do
      explainBoolAndBottom first second
      return (Pattern.fromTermLike second)
  | isTop second    = return (Pattern.fromTermLike first)
  | otherwise       = empty

explainBoolAndBottom
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier ()
explainBoolAndBottom term1 term2 =
    lift $ explainBottom "Cannot unify bottom." term1 term2

-- | Unify two identical ('==') patterns.
equalAndEquals
    :: InternalVariable RewritingVariableName
    => Monad unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
equalAndEquals first second =
    if first == second then
        -- TODO (thomas.tuegel): Preserve simplified flags.
        return (Pattern.fromTermLike first)
    else empty

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals
    :: MonadUnify unifier
    => SideCondition RewritingVariableName
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
bottomTermEquals
    sideCondition
    first@(Bottom_ _)
    second
  = lift $ do -- MonadUnify
    secondCeil <- makeEvaluateTermCeil sideCondition second
    case toList secondCeil of
        [] -> return Pattern.top
        [ Conditional { predicate = PredicateTrue, substitution } ]
          | substitution == mempty -> do
            explainBottom
                "Cannot unify bottom with non-bottom pattern."
                first
                second
            empty
        _ ->
            return  Conditional
                { term = mkTop_
                , predicate =
                    makeNotPredicate
                    $ OrCondition.toPredicate
                    $ OrPattern.map Condition.toPredicate secondCeil
                , substitution = mempty
                }
bottomTermEquals _ _ _ = empty

{- | Unify two patterns where the second is @\\bottom@.

See also: 'bottomTermEquals'

 -}
termBottomEquals
    :: MonadUnify unifier
    => SideCondition RewritingVariableName
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
termBottomEquals sideCondition first second =
    bottomTermEquals sideCondition second first

variableFunctionAnd
    :: InternalVariable variable
    => MonadUnify unifier
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
variableFunctionAnd
    (ElemVar_ v1)
    second@(ElemVar_ _)
  = return $ Pattern.assign (inject v1) second
variableFunctionAnd
    (ElemVar_ v)
    second
  | isFunctionPattern second =
    -- Ceil predicate not needed since 'second' being bottom
    -- will make the entire term bottom. However, one must
    -- be careful to not just drop the term.
    lift $ return (Pattern.withCondition second result)
  where result = Condition.fromSingleSubstitution
            (Substitution.assign (inject v) second)
variableFunctionAnd _ _ = empty

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

 -}
variableFunctionEquals
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
variableFunctionEquals
    first@(ElemVar_ v)
    second
  | isFunctionPattern second = lift $ do -- MonadUnify
    predicate <- do
        resultOr <- makeEvaluateTermCeil SideCondition.topTODO second
        case toList resultOr of
            [] -> do
                explainBottom
                    "Unification of variable and bottom \
                    \when attempting to simplify equals."
                    first
                    second
                empty
            resultConditions -> Unify.scatter resultConditions
    let result =
            predicate
            <> Condition.fromSingleSubstitution
                (Substitution.assign (inject v) second)
    return (Pattern.withCondition second result)
variableFunctionEquals _ _ = empty

{- | Simplify the conjunction of two sort injections.

Assumes that the two heads were already tested for equality and were found
to be different.

This simplifies cases where there is a subsort relation between the injected
sorts of the conjoined patterns, such as,

@
    \inj{src1, dst}(a) ∧ \inj{src2, dst}(b)
    ===
    \inj{src2, dst}(\inj{src1, src2}(a) ∧ b)
@

when @src1@ is a subsort of @src2@.

 -}
sortInjectionAndEquals
    :: forall unifier
    .  MonadUnify unifier
    => TermSimplifier RewritingVariableName unifier
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
sortInjectionAndEquals termMerger first@(Inj_ inj1) second@(Inj_ inj2) = do
    InjSimplifier { unifyInj } <- Simplifier.askInjSimplifier
    unifyInj inj1 inj2 & either distinct merge
  where
    emptyIntersection = explainAndReturnBottom "Empty sort intersection"
    distinct Distinct = lift $ emptyIntersection first second
    distinct Unknown = empty
    merge inj@Inj { injChild = Pair child1 child2 } = lift $ do
        childPattern <- termMerger child1 child2
        InjSimplifier { evaluateInj } <- askInjSimplifier
        let (childTerm, childCondition) = Pattern.splitTerm childPattern
            inj' = evaluateInj inj { injChild = childTerm }
        return $ Pattern.withCondition inj' childCondition
sortInjectionAndEquals _ _ _ = empty

{- | Unify a constructor application pattern with a sort injection pattern.

Sort injections clash with constructors, so @constructorSortInjectionAndEquals@
returns @\\bottom@.

 -}
constructorSortInjectionAndEquals
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier a
constructorSortInjectionAndEquals first@(Inj_ _) second@(App_ symbol2 _)
  | Symbol.isConstructor symbol2 =
    lift $ noConfusionInjectionConstructor first second
constructorSortInjectionAndEquals first@(App_ symbol1 _) second@(Inj_ _)
  | Symbol.isConstructor symbol1 =
    lift $ noConfusionInjectionConstructor first second
constructorSortInjectionAndEquals _ _ = empty

noConfusionInjectionConstructor
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> unifier a
noConfusionInjectionConstructor =
    explainAndReturnBottom "No confusion: sort injections and constructors"

{- |
 If the two constructors form an overload pair, apply the overloading axioms
 on the terms to make the constructors equal, then retry unification on them.

See <https://github.com/kframework/kore/blob/master/docs/2019-08-27-Unification-modulo-overloaded-constructors.md>

 -}
overloadedConstructorSortInjectionAndEquals
    :: MonadUnify unifier
    => TermSimplifier RewritingVariableName unifier
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
overloadedConstructorSortInjectionAndEquals termMerger firstTerm secondTerm
  = do
    eunifier <- lift . Error.runExceptT
        $ unifyOverloading (Pair firstTerm secondTerm)
    case eunifier of
        Right (Simple (Pair firstTerm' secondTerm')) -> lift $
            termMerger firstTerm' secondTerm'
        Right
            (WithNarrowing Narrowing
                { narrowingSubst
                , narrowingVars
                , overloadPair = Pair firstTerm' secondTerm'
                }
            ) -> do
                boundPattern <- lift $ do
                    merged <- termMerger firstTerm' secondTerm'
                    Exists.makeEvaluate SideCondition.topTODO narrowingVars
                        $ merged `Pattern.andCondition` narrowingSubst
                case OrPattern.toPatterns boundPattern of
                    [result] -> return result
                    [] -> lift $
                        explainAndReturnBottom
                            (  "exists simplification for overloaded"
                            <> " constructors returned no pattern"
                            )
                            firstTerm
                            secondTerm
                    _ -> empty
        Left (Clash message) -> lift $
            explainAndReturnBottom (fromString message) firstTerm secondTerm
        Left Overloading.NotApplicable -> empty

{- | Unifcation or equality for a domain value pattern vs a constructor
application.

This unification case throws an error because domain values may not occur in a
sort with constructors.

-}
domainValueAndConstructorErrors
    :: Monad unifier
    => HasCallStack
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier a
domainValueAndConstructorErrors
    term1@(DV_ _ _)
    term2@(App_ secondHead _)
    | Symbol.isConstructor secondHead =
      error (unlines [ "Cannot handle DomainValue and Constructor:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors
    term1@(App_ firstHead _)
    term2@(DV_ _ _)
    | Symbol.isConstructor firstHead =
      error (unlines [ "Cannot handle Constructor and DomainValue:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )
domainValueAndConstructorErrors _ _ = empty

{- | Unify two domain values.

The two patterns are assumed to be inequal; therefore this case always return
@\\bottom@.

See also: 'equalAndEquals'

-}
-- TODO (thomas.tuegel): This unification case assumes that \dv is injective,
-- but it is not.
unifyDomainValue
    :: forall unifier
    .  HasCallStack
    => MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyDomainValue term1@(DV_ sort1 value1) term2@(DV_ sort2 value2) =
    assert (sort1 == sort2) $ lift worker
  where
    worker :: unifier (Pattern RewritingVariableName)
    worker
      | value1 == value2 =
        return $ Pattern.fromTermLike term1
      | otherwise = cannotUnifyDomainValues term1 term2
unifyDomainValue _ _ = empty

cannotUnifyDistinctDomainValues :: Pretty.Doc ()
cannotUnifyDistinctDomainValues = "distinct domain values"

cannotUnifyDomainValues
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> unifier a
cannotUnifyDomainValues = explainAndReturnBottom cannotUnifyDistinctDomainValues

{-| Unify two literal strings.

The two patterns are assumed to be inequal; therefore this case always returns
@\\bottom@.

See also: 'equalAndEquals'

 -}
unifyStringLiteral
    :: forall unifier
    .  MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyStringLiteral term1@(StringLiteral_ _) term2@(StringLiteral_ _) = lift worker
  where
    worker :: unifier (Pattern RewritingVariableName)
    worker
      | term1 == term2 =
        return $ Pattern.fromTermLike term1
      | otherwise = explainAndReturnBottom "distinct string literals" term1 term2
unifyStringLiteral _ _ = empty

{- | Unify any two function patterns.

The function patterns are unified by creating an @\\equals@ predicate. If either
argument is constructor-like, that argument will be the resulting 'term';
otherwise, the lesser argument is the resulting 'term'. The term always appears
on the left-hand side of the @\\equals@ predicate, and the other argument
appears on the right-hand side.

-}
functionAnd
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe (Pattern RewritingVariableName)
functionAnd first second
  | isFunctionPattern first, isFunctionPattern second =
    makeEqualsPredicate first' second'
    & Predicate.markSimplified
    -- Ceil predicate not needed since first being
    -- bottom will make the entire term bottom. However,
    -- one must be careful to not just drop the term.
    & Condition.fromPredicate
    & Pattern.withCondition first'  -- different for Equals
    & pure
  | otherwise = empty
  where
    (first', second') = minMaxBy compareForEquals first second


{- | Normal ordering for terms in @\equals(_, _)@.

The normal ordering is arbitrary, but important to avoid duplication.

-}
compareForEquals
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Ordering
compareForEquals first second
  | isConstructorLike first = LT
  | isConstructorLike second = GT
  | otherwise = compare first second

bytesDifferent
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
bytesDifferent
    (Recursive.project -> _ :< InternalBytesF (Const bytesFirst))
    (Recursive.project -> _ :< InternalBytesF (Const bytesSecond))
  | bytesFirst /= bytesSecond
    = return Pattern.bottom
bytesDifferent _ _ = empty
