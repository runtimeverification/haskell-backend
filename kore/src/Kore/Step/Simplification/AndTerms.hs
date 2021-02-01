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
    , equalsFunctions
    , andFunctions
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
import qualified Kore.Step.Simplification.Exists as Exists
import Kore.Step.Simplification.ExpandAlias
    ( expandAlias
    )
import Kore.Step.Simplification.InjSimplifier
import Kore.Step.Simplification.NoConfusion
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Overloading as Overloading
import Kore.Step.Simplification.SimplificationType
    ( SimplificationType
    )
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

data SimplificationTarget = AndT | EqualsT | BothT

{- | Unify two terms without discarding the terms.

We want to keep the terms because substitution relies on the result not being
@\\bottom@.

When a case is not implemented, @termUnification@ will create a @\\ceil@ of
the conjunction of the two terms.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.

-}
termUnification
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> TermLike variable
    -> TermLike variable
    -> unifier (Pattern variable)
termUnification notSimplifier = \term1 term2 ->
    whileDebugUnification term1 term2 $ do
        result <- termUnificationWorker term1 term2
        debugUnificationSolved result
        pure result
  where
    termUnificationWorker
        :: TermLike variable
        -> TermLike variable
        -> unifier (Pattern variable)
    termUnificationWorker pat1 pat2 = do
        let
            maybeTermUnification :: MaybeT unifier (Pattern variable)
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
    :: InternalVariable variable
    => MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTermEquals notSimplifier =
    maybeTransformTerm (equalsFunctions notSimplifier)

maybeTermAnd
    :: InternalVariable variable
    => MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm "and".
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTermAnd notSimplifier =
    maybeTransformTerm (andFunctions notSimplifier)

andFunctions
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> [TermTransformationOld variable unifier]
andFunctions notSimplifier =
    forAnd . snd
    <$> filter appliesToAnd (andEqualsFunctions notSimplifier)
  where
    appliesToAnd :: (SimplificationTarget, a) -> Bool
    appliesToAnd (AndT, _) = True
    appliesToAnd (EqualsT, _) = False
    appliesToAnd (BothT, _) = True

    forAnd
        :: TermTransformation variable unifier
        -> TermTransformationOld variable unifier
    forAnd f = f SideCondition.topTODO SimplificationType.And

equalsFunctions
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> [TermTransformationOld variable unifier]
equalsFunctions notSimplifier =
    forEquals . snd
    <$> filter appliesToEquals (andEqualsFunctions notSimplifier)
  where
    appliesToEquals :: (SimplificationTarget, a) -> Bool
    appliesToEquals (AndT, _) = False
    appliesToEquals (EqualsT, _) = True
    appliesToEquals (BothT, _) = True

    forEquals
        :: TermTransformation variable unifier
        -> TermTransformationOld variable unifier
    forEquals f = f SideCondition.topTODO SimplificationType.Equals

andEqualsFunctions
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> [(SimplificationTarget, TermTransformation variable unifier)]
andEqualsFunctions notSimplifier =
    [ (AndT,    \_ _ s -> expandAlias (maybeTermAnd notSimplifier s))
    , (AndT,    \_ _ _ -> boolAnd)
    , (BothT,   \_ _ _ -> Builtin.Int.unifyInt)
    , (BothT,   \_ _ _ -> Builtin.Bool.unifyBool)
    , (BothT,   \_ _ _ -> Builtin.String.unifyString)
    , (BothT,   \_ _ _ -> unifyDomainValue)
    , (BothT,   \_ _ _ -> unifyStringLiteral)
    , (BothT,   \_ _ _ -> equalAndEquals)
    , (BothT,   \_ _ _ -> bytesDifferent)
    , (EqualsT, \p _ _ -> bottomTermEquals p)
    , (EqualsT, \p _ _ -> termBottomEquals p)
    , (BothT,   \p t _ -> variableFunctionAndEquals p t)
    , (BothT,   \p t _ -> functionVariableAndEquals p t)
    , (BothT,   \_ _ s -> equalInjectiveHeadsAndEquals s)
    , (BothT,   \_ _ s -> sortInjectionAndEquals s)
    , (BothT,   \_ _ _ -> constructorSortInjectionAndEquals)
    , (BothT,   \_ _ _ -> constructorAndEqualsAssumesDifferentHeads)
    , (BothT,   \_ _ s -> overloadedConstructorSortInjectionAndEquals s)
    , (BothT,   \_ _ s -> Builtin.Bool.unifyBoolAnd s)
    , (BothT,   \_ _ s -> Builtin.Bool.unifyBoolOr s)
    , (BothT,   \_ _ s -> Builtin.Bool.unifyBoolNot s)
    , (EqualsT, \_ _ s -> Builtin.Int.unifyIntEq s notSimplifier)
    , (EqualsT, \_ _ s -> Builtin.String.unifyStringEq s notSimplifier)
    , (BothT,   \_ _ s -> Builtin.KEqual.unifyKequalsEq s notSimplifier)
    , (AndT,    \_ _ s -> Builtin.KEqual.unifyIfThenElse s)
    , (BothT,   \_ _ _ -> Builtin.Endianness.unifyEquals)
    , (BothT,   \_ _ _ -> Builtin.Signedness.unifyEquals)
    , (EqualsT, \_ _ s -> Builtin.Map.unifyNotInKeys s notSimplifier)
    , (BothT,   \_ t s -> Builtin.List.unifyEquals t s)
    , (BothT,   \_ _ _ -> domainValueAndConstructorErrors)
    , (AndT,    \_ _ _ t1 t2 -> Error.hoistMaybe $ functionAnd t1 t2)
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
type TermTransformation variable unifier =
       SideCondition variable
    -> SimplificationType
    -> TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)

type TermTransformationOld variable unifier =
       TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)

maybeTransformTerm
    :: MonadUnify unifier
    => [TermTransformationOld variable unifier]
    -> TermSimplifier variable unifier
    -- ^ Used to simplify subterm pairs.
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
maybeTransformTerm topTransformers childTransformers first second =
    asum
        (map
            (\f -> f
                childTransformers
                first
                second
            )
            topTransformers
        )

-- | Simplify the conjunction of terms where one is a predicate.
boolAnd
    :: MonadUnify unifier
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
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
    => InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier ()
explainBoolAndBottom term1 term2 =
    lift $ explainBottom "Cannot unify bottom." term1 term2

-- | Unify two identical ('==') patterns.
equalAndEquals
    :: InternalVariable variable
    => Monad unifier
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
equalAndEquals first second
  | first == second =
    -- TODO (thomas.tuegel): Preserve defined and simplified flags.
    return (Pattern.fromTermLike first)
equalAndEquals _ _ = empty

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals
    :: InternalVariable variable
    => MonadUnify unifier
    => SideCondition variable
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
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
    :: InternalVariable variable
    => MonadUnify unifier
    => SideCondition variable
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
termBottomEquals sideCondition first second =
    bottomTermEquals sideCondition second first

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

 -}
variableFunctionAndEquals
    :: InternalVariable variable
    => MonadUnify unifier
    => SideCondition variable
    -> SimplificationType
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
variableFunctionAndEquals
    _
    SimplificationType.And
    (ElemVar_ v1)
    second@(ElemVar_ _)
  =
      return $ Pattern.assign (inject v1) second
variableFunctionAndEquals
    sideCondition
    simplificationType
    first@(ElemVar_ v)
    second
  | isFunctionPattern second = lift $ do -- MonadUnify
    predicate <-
        case simplificationType of -- Simplifier
            SimplificationType.And ->
                -- Ceil predicate not needed since 'second' being bottom
                -- will make the entire term bottom. However, one must
                -- be careful to not just drop the term.
                return Condition.top
            SimplificationType.Equals -> do
                resultOr <- makeEvaluateTermCeil sideCondition second
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
variableFunctionAndEquals _ _ _ _ = empty

{- | Unify a function pattern with a variable.

See also: 'variableFunctionAndEquals'

 -}
functionVariableAndEquals
    :: (InternalVariable variable, MonadUnify unifier)
    => SideCondition variable
    -> SimplificationType
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
functionVariableAndEquals sideCondition simplificationType first second =
    variableFunctionAndEquals sideCondition simplificationType second first

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
    ::  forall variable unifier
    .   ( InternalVariable variable
        , MonadUnify unifier
        )
    => TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
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
    :: InternalVariable variable
    => MonadUnify unifier
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier a
constructorSortInjectionAndEquals first@(Inj_ _) second@(App_ symbol2 _)
  | Symbol.isConstructor symbol2 =
    lift $ noConfusionInjectionConstructor first second
constructorSortInjectionAndEquals first@(App_ symbol1 _) second@(Inj_ _)
  | Symbol.isConstructor symbol1 =
    lift $ noConfusionInjectionConstructor first second
constructorSortInjectionAndEquals _ _ = empty

noConfusionInjectionConstructor
    :: InternalVariable variable
    => MonadUnify unifier
    => TermLike variable
    -> TermLike variable
    -> unifier a
noConfusionInjectionConstructor =
    explainAndReturnBottom "No confusion: sort injections and constructors"

{- |
 If the two constructors form an overload pair, apply the overloading axioms
 on the terms to make the constructors equal, then retry unification on them.

See <https://github.com/kframework/kore/blob/master/docs/2019-08-27-Unification-modulo-overloaded-constructors.md>

 -}
overloadedConstructorSortInjectionAndEquals
    :: (InternalVariable variable, MonadUnify unifier)
    => TermSimplifier variable unifier
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
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
    :: InternalVariable variable
    => Monad unifier
    => HasCallStack
    => TermLike variable
    -> TermLike variable
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
    :: forall variable unifier
    .  HasCallStack
    => InternalVariable variable
    => MonadUnify unifier
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
unifyDomainValue term1@(DV_ sort1 value1) term2@(DV_ sort2 value2) =
    assert (sort1 == sort2) $ lift worker
  where
    worker :: unifier (Pattern variable)
    worker
      | value1 == value2 =
        return $ Pattern.fromTermLike term1
      | otherwise = cannotUnifyDomainValues term1 term2
unifyDomainValue _ _ = empty

cannotUnifyDistinctDomainValues :: Pretty.Doc ()
cannotUnifyDistinctDomainValues = "distinct domain values"

cannotUnifyDomainValues
    :: InternalVariable variable
    => MonadUnify unifier
    => TermLike variable
    -> TermLike variable
    -> unifier a
cannotUnifyDomainValues = explainAndReturnBottom cannotUnifyDistinctDomainValues

{-| Unify two literal strings.

The two patterns are assumed to be inequal; therefore this case always returns
@\\bottom@.

See also: 'equalAndEquals'

 -}
unifyStringLiteral
    :: forall variable unifier
    .  InternalVariable variable
    => MonadUnify unifier
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
unifyStringLiteral term1@(StringLiteral_ _) term2@(StringLiteral_ _) = lift worker
  where
    worker :: unifier (Pattern variable)
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
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Maybe (Pattern variable)
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
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> Ordering
compareForEquals first second
  | isConstructorLike first = LT
  | isConstructorLike second = GT
  | otherwise = compare first second

bytesDifferent
    :: InternalVariable variable
    => MonadUnify unifier
    => TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
bytesDifferent
    (Recursive.project -> _ :< InternalBytesF (Const bytesFirst))
    (Recursive.project -> _ :< InternalBytesF (Const bytesSecond))
  | bytesFirst /= bytesSecond
    = return Pattern.bottom
bytesDifferent _ _ = empty
