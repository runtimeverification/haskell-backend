{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.AndTerms (
    termUnification,
    maybeTermAnd,
    maybeTermEquals,
    TermSimplifier,
    TermTransformationOld,
    cannotUnifyDistinctDomainValues,
    functionAnd,
    compareForEquals,
) where

import Control.Error (
    MaybeT (..),
 )
import qualified Control.Error as Error
import Data.String (
    fromString,
 )
import Data.Text (
    Text,
 )
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Endianness as Builtin.Endianness
import qualified Kore.Builtin.Int as Builtin.Int
import Kore.Builtin.InternalBytes (
    matchBytes,
    unifyBytes,
 )
import qualified Kore.Builtin.KEqual as Builtin.KEqual
import qualified Kore.Builtin.List as Builtin.List
import qualified Kore.Builtin.Map as Builtin.Map
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Builtin.Signedness as Builtin.Signedness
import qualified Kore.Builtin.String as Builtin.String
import Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrCondition as OrCondition
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeEqualsPredicate,
    makeNotPredicate,
    pattern PredicateTrue,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    topTODO,
 )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import Kore.Log.DebugUnification (
    debugUnificationSolved,
    debugUnificationUnsolved,
    whileDebugUnification,
 )
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottom,
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.Simplification.Exists as Exists
import Kore.Step.Simplification.ExpandAlias
import Kore.Step.Simplification.InjSimplifier
import Kore.Step.Simplification.NoConfusion
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.OverloadSimplifier as OverloadSimplifier
import Kore.Step.Simplification.Overloading as Overloading
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Unification.Unify as Unify
import Kore.Unparser
import Pair
import Prelude.Kore

{- | Unify two terms without discarding the terms.

We want to keep the terms because substitution relies on the result not being
@\\bottom@.

When a case is not implemented, @termUnification@ will create a @\\ceil@ of
the conjunction of the two terms.

The comment for 'Kore.Step.Simplification.And.simplify' describes all
the special cases handled by this.
-}
termUnification ::
    forall unifier.
    MonadUnify unifier =>
    HasCallStack =>
    NotSimplifier unifier ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    unifier (Pattern RewritingVariableName)
termUnification notSimplifier = \term1 term2 ->
    whileDebugUnification term1 term2 $ do
        result <- termUnificationWorker term1 term2
        debugUnificationSolved result
        pure result
  where
    termUnificationWorker ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        unifier (Pattern RewritingVariableName)
    termUnificationWorker pat1 pat2 = do
        let maybeTermUnification ::
                MaybeT unifier (Pattern RewritingVariableName)
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

maybeTermEquals ::
    MonadUnify unifier =>
    HasCallStack =>
    NotSimplifier unifier ->
    -- | Used to simplify subterm "and".
    TermSimplifier RewritingVariableName unifier ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MaybeT unifier (Pattern RewritingVariableName)
maybeTermEquals notSimplifier childTransformers first second = do
    injSimplifier <- Simplifier.askInjSimplifier
    OverloadSimplifier{isOverloaded} <- Simplifier.askOverloadSimplifier
    worker injSimplifier isOverloaded
  where
    worker injSimplifier isOverloaded
        | Just unifyData <- Builtin.Int.matchInt first second =
            lift $ Builtin.Int.unifyInt first second unifyData
        | Just unifyData <- Builtin.Bool.matchBools first second =
            lift $ Builtin.Bool.unifyBool first second unifyData
        | Just unifyData <- Builtin.String.matchString first second =
            lift $ Builtin.String.unifyString first second unifyData
        | Just unifyData <- matchDomainValue first second =
            lift $ unifyDomainValue first second unifyData
        | Just unifyData <- matchStringLiteral first second =
            lift $ unifyStringLiteral first second unifyData
        | Just () <- matchEqualsAndEquals first second =
            lift $ equalAndEquals first
        | Just unifyData <- matchBytes first second =
            lift $ unifyBytes unifyData
        | Just () <- matchBottomTermEquals first =
            lift $ bottomTermEquals SideCondition.topTODO first second
        | Just () <- matchBottomTermEquals second =
            lift $ bottomTermEquals SideCondition.topTODO second first
        | Just var <- matchVariableFunctionEquals first second =
            lift $ variableFunctionEquals first second var
        | Just var <- matchVariableFunctionEquals second first =
            lift $ variableFunctionEquals second first var
        | Just unifyData <- matchEqualInjectiveHeadsAndEquals first second =
            lift $ equalInjectiveHeadsAndEquals childTransformers unifyData
        | Just unifyData <- matchInj injSimplifier first second =
            lift $ unifySortInjection childTransformers first second unifyData
        | Just () <- matchConstructorSortInjectionAndEquals first second =
            lift $ constructorSortInjectionAndEquals first second
        | Just () <- matchDifferentConstructors isOverloaded first second =
            lift $ constructorAndEqualsAssumesDifferentHeads first second
        | otherwise =
            overloadedConstructorSortInjectionAndEquals childTransformers first second
                <|> rest

    rest
        | Just boolAndData <- Builtin.Bool.matchUnifyBoolAnd first second =
            lift $ Builtin.Bool.unifyBoolAnd childTransformers first boolAndData
        | Just boolAndData <- Builtin.Bool.matchUnifyBoolAnd second first =
            lift $ Builtin.Bool.unifyBoolAnd childTransformers second boolAndData
        | Just boolOrData <- Builtin.Bool.matchUnifyBoolOr first second =
            lift $ Builtin.Bool.unifyBoolOr childTransformers first boolOrData
        | Just boolOrData <- Builtin.Bool.matchUnifyBoolOr second first =
            lift $ Builtin.Bool.unifyBoolOr childTransformers second boolOrData
        | Just boolNotData <- Builtin.Bool.matchUnifyBoolNot first second =
            lift $ Builtin.Bool.unifyBoolNot childTransformers first boolNotData
        | Just boolNotData <- Builtin.Bool.matchUnifyBoolNot second first =
            lift $ Builtin.Bool.unifyBoolNot childTransformers second boolNotData
        | Just unifyData <- Builtin.Int.matchUnifyIntEq first second =
            lift $ Builtin.Int.unifyIntEq childTransformers notSimplifier unifyData
        | Just unifyData <- Builtin.Int.matchUnifyIntEq second first =
            lift $ Builtin.Int.unifyIntEq childTransformers notSimplifier unifyData
        | Just unifyData <- Builtin.String.matchUnifyStringEq first second = lift $ Builtin.String.unifyStringEq childTransformers notSimplifier unifyData
        | Just unifyData <- Builtin.String.matchUnifyStringEq second first = lift $ Builtin.String.unifyStringEq childTransformers notSimplifier unifyData
        | otherwise =
            asum
                [ do
                    unifyData <- Error.hoistMaybe $ Builtin.KEqual.matchUnifyKequalsEq first second
                    lift $ Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier unifyData
                , do
                    unifyData <- Error.hoistMaybe $ Builtin.KEqual.matchUnifyKequalsEq second first
                    lift $ Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier unifyData
                , Builtin.Endianness.unifyEquals first second
                , Builtin.Signedness.unifyEquals first second
                , Builtin.Map.unifyEquals childTransformers first second
                , Builtin.Map.unifyNotInKeys childTransformers notSimplifier first second
                , Builtin.Set.unifyEquals childTransformers first second
                , Builtin.List.unifyEquals childTransformers first second
                , domainValueAndConstructorErrors first second
                ]

maybeTermAnd ::
    MonadUnify unifier =>
    HasCallStack =>
    NotSimplifier unifier ->
    -- | Used to simplify subterm "and".
    TermSimplifier RewritingVariableName unifier ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MaybeT unifier (Pattern RewritingVariableName)
maybeTermAnd notSimplifier childTransformers first second = do
    injSimplifier <- Simplifier.askInjSimplifier
    OverloadSimplifier{isOverloaded} <- Simplifier.askOverloadSimplifier
    worker injSimplifier isOverloaded
  where
    worker injSimplifier isOverloaded
        | Just unifyData <- matchExpandAlias first second =
            let UnifyExpandAlias{term1, term2} = unifyData
             in maybeTermAnd
                    notSimplifier
                    childTransformers
                    term1
                    term2
        | Just unifyData <- matchBoolAnd first =
            lift $ boolAnd first second unifyData
        | Just unifyData <- matchBoolAnd second =
            lift $ boolAnd second first unifyData
        | Just unifyData <- Builtin.Int.matchInt first second =
            lift $ Builtin.Int.unifyInt first second unifyData
        | Just unifyData <- Builtin.Bool.matchBools first second =
            lift $ Builtin.Bool.unifyBool first second unifyData
        | Just unifyData <- Builtin.String.matchString first second =
            lift $ Builtin.String.unifyString first second unifyData
        | Just unifyData <- matchDomainValue first second =
            lift $ unifyDomainValue first second unifyData
        | Just unifyData <- matchStringLiteral first second =
            lift $ unifyStringLiteral first second unifyData
        | Just () <- matchEqualsAndEquals first second =
            lift $ equalAndEquals first
        | Just unifyData <- matchBytes first second =
            lift $ unifyBytes unifyData
        | Just matched <- matchVariables first second =
            lift $ unifyVariables matched
        | Just matched <- matchVariableFunction second first =
            lift $ unifyVariableFunction matched
        | Just unifyData <- matchEqualInjectiveHeadsAndEquals first second =
            lift $ equalInjectiveHeadsAndEquals childTransformers unifyData
        | Just unifyData <- matchInj injSimplifier first second =
            lift $ unifySortInjection childTransformers first second unifyData
        | Just () <- matchConstructorSortInjectionAndEquals first second =
            lift $ constructorSortInjectionAndEquals first second
        | Just () <- matchDifferentConstructors isOverloaded first second =
            lift $ constructorAndEqualsAssumesDifferentHeads first second
        | otherwise =
            overloadedConstructorSortInjectionAndEquals childTransformers first second
                <|> rest

    rest
        | Just boolAndData <- Builtin.Bool.matchUnifyBoolAnd first second =
            lift $ Builtin.Bool.unifyBoolAnd childTransformers first boolAndData
        | Just boolAndData <- Builtin.Bool.matchUnifyBoolAnd second first =
            lift $ Builtin.Bool.unifyBoolAnd childTransformers second boolAndData
        | Just boolOrData <- Builtin.Bool.matchUnifyBoolOr first second =
            lift $ Builtin.Bool.unifyBoolOr childTransformers first boolOrData
        | Just boolOrData <- Builtin.Bool.matchUnifyBoolOr second first =
            lift $ Builtin.Bool.unifyBoolOr childTransformers second boolOrData
        | Just boolNotData <- Builtin.Bool.matchUnifyBoolNot first second =
            lift $ Builtin.Bool.unifyBoolNot childTransformers first boolNotData
        | Just boolNotData <- Builtin.Bool.matchUnifyBoolNot second first =
            lift $ Builtin.Bool.unifyBoolNot childTransformers second boolNotData
        | Just unifyData <- Builtin.KEqual.matchUnifyKequalsEq first second =
            lift $ Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier unifyData
        | Just unifyData <- Builtin.Int.matchUnifyIntEq first second =
            lift $ Builtin.Int.unifyIntEq childTransformers notSimplifier unifyData
        | Just unifyData <- Builtin.String.matchUnifyStringEq first second = lift $ Builtin.String.unifyStringEq childTransformers notSimplifier unifyData
        | otherwise =
            asum
                [ Builtin.KEqual.unifyIfThenElse childTransformers first second
                , Builtin.Endianness.unifyEquals first second
                , Builtin.Signedness.unifyEquals first second
                , Builtin.Map.unifyEquals childTransformers first second
                , Builtin.Set.unifyEquals childTransformers first second
                , Builtin.List.unifyEquals childTransformers first second
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
    TermSimplifier variable unifier ->
    TermLike variable ->
    TermLike variable ->
    MaybeT unifier (Pattern variable)

data UnifyBoolAnd
    = UnifyBoolAndBottom
    | UnifyBoolAndTop

{- | Matches

@
\\and{_}(\\bottom, _)
@

and

@
\\and{_}(\\top, _)
@
-}
matchBoolAnd ::
    TermLike RewritingVariableName ->
    Maybe UnifyBoolAnd
matchBoolAnd term
    | Pattern.isBottom term =
        Just UnifyBoolAndBottom
    | Pattern.isTop term =
        Just UnifyBoolAndTop
    | otherwise =
        Nothing
{-# INLINE matchBoolAnd #-}

-- | Simplify the conjunction of terms where one is a predicate.
boolAnd ::
    MonadUnify unifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    UnifyBoolAnd ->
    unifier (Pattern RewritingVariableName)
boolAnd first second unifyData =
    case unifyData of
        UnifyBoolAndBottom -> do
            explainBoolAndBottom first second
            return $ Pattern.fromTermLike first
        UnifyBoolAndTop ->
            return $ Pattern.fromTermLike second

explainBoolAndBottom ::
    MonadUnify unifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    unifier ()
explainBoolAndBottom term1 term2 =
    debugUnifyBottom "Cannot unify bottom." term1 term2

{- | Matches

@
\\equals{_, _}(t, t)
@

and

@
\\and{_}(t, t)
@
-}
matchEqualsAndEquals ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe ()
matchEqualsAndEquals first second
    | first == second =
        Just ()
    | otherwise = Nothing
{-# INLINE matchEqualsAndEquals #-}

-- | Returns the term as a pattern.
equalAndEquals ::
    Monad unifier =>
    TermLike RewritingVariableName ->
    unifier (Pattern RewritingVariableName)
equalAndEquals first =
    -- TODO (thomas.tuegel): Preserve simplified flags.
    return (Pattern.fromTermLike first)

{- | Matches

@
\\equals{_, _}(\\bottom, _)
@
-}
matchBottomTermEquals ::
    TermLike RewritingVariableName ->
    Maybe ()
matchBottomTermEquals first
    | Bottom_ _ <- first =
        Just ()
    | otherwise = Nothing
{-# INLINE matchBottomTermEquals #-}

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals ::
    MonadUnify unifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    unifier (Pattern RewritingVariableName)
bottomTermEquals
    sideCondition
    first
    second =
        do
            -- MonadUnify
            secondCeil <- makeEvaluateTermCeil sideCondition second
            case toList secondCeil of
                [] -> return Pattern.top
                [Conditional{predicate = PredicateTrue, substitution}]
                    | substitution == mempty -> do
                        debugUnifyBottomAndReturnBottom
                            "Cannot unify bottom with non-bottom pattern."
                            first
                            second
                _ ->
                    return
                        Conditional
                            { term = mkTop_
                            , predicate =
                                makeNotPredicate $
                                    OrCondition.toPredicate $
                                        OrPattern.map Condition.toPredicate secondCeil
                            , substitution = mempty
                            }

data UnifyVariables = UnifyVariables
    {variable1, variable2 :: !(ElementVariable RewritingVariableName)}

-- | Match the unification of two element variables.
matchVariables ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyVariables
matchVariables first second = do
    ElemVar_ variable1 <- pure first
    ElemVar_ variable2 <- pure second
    pure UnifyVariables{variable1, variable2}
{-# INLINE matchVariables #-}

unifyVariables ::
    MonadUnify unifier =>
    UnifyVariables ->
    unifier (Pattern RewritingVariableName)
unifyVariables UnifyVariables{variable1, variable2} =
    pure $ Pattern.assign (inject variable1) (mkElemVar variable2)

data UnifyVariableFunction = UnifyVariableFunction
    { variable :: !(ElementVariable RewritingVariableName)
    , term :: !(TermLike RewritingVariableName)
    }

-- | Match the unification of an element variable with a function-like term.
matchVariableFunction ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyVariableFunction
matchVariableFunction = \first second ->
    worker first second <|> worker second first
  where
    worker first term = do
        ElemVar_ variable <- pure first
        guard (isFunctionPattern term)
        pure UnifyVariableFunction{variable, term}
{-# INLINE matchVariableFunction #-}

unifyVariableFunction ::
    MonadUnify unifier =>
    UnifyVariableFunction ->
    unifier (Pattern RewritingVariableName)
unifyVariableFunction UnifyVariableFunction{variable, term} =
    Condition.assign (inject variable) term
        & Pattern.withCondition term
        & pure

{- | Matches

@
\\equals{_, _}(x, f(_))
@
-}
matchVariableFunctionEquals ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe (ElementVariable RewritingVariableName)
matchVariableFunctionEquals first second
    | ElemVar_ var <- first
      , isFunctionPattern second =
        Just var
    | otherwise = Nothing
{-# INLINE matchVariableFunctionEquals #-}

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'
-}
variableFunctionEquals ::
    MonadUnify unifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    ElementVariable RewritingVariableName ->
    unifier (Pattern RewritingVariableName)
variableFunctionEquals
    first
    second
    var =
        do
            -- MonadUnify
            predicate <- do
                resultOr <- makeEvaluateTermCeil SideCondition.topTODO second
                case toList resultOr of
                    [] -> do
                        debugUnifyBottomAndReturnBottom
                            "Unification of variable and bottom \
                            \when attempting to simplify equals."
                            first
                            second
                    resultConditions -> Unify.scatter resultConditions
            let result =
                    predicate
                        <> Condition.fromSingleSubstitution
                            (Substitution.assign (inject var) second)
            return (Pattern.withCondition second result)

{- | Matches

@
\\equals{_, _}(inj{sub, super}(children), inj{sub', super'}(children'))
@

and

@
\\and{_}(inj{sub, super}(children), inj{sub', super'}(children'))
@

when either

* @super /= super'@
* @sub == sub'@
* @sub@ is a subsort of @sub'@ or vice-versa.
* @children@ or @children'@ satisfies @hasConstructorLikeTop@.
* the subsorts of @sub, sub'@ are disjoint.
-}
matchInj ::
    InjSimplifier ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe (UnifyInj (InjPair RewritingVariableName))
matchInj injSimplifier first second
    | Inj_ inj1 <- first
      , Inj_ inj2 <- second =
        matchInjs injSimplifier inj1 inj2
    | otherwise = Nothing
{-# INLINE matchInj #-}

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
unifySortInjection ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    UnifyInj (InjPair RewritingVariableName) ->
    unifier (Pattern RewritingVariableName)
unifySortInjection termMerger term1 term2 unifyInj = do
    InjSimplifier{unifyInjs} <- Simplifier.askInjSimplifier
    unifyInjs unifyInj & maybe distinct merge
  where
    distinct =
        debugUnifyBottomAndReturnBottom "Distinct sort injections" term1 term2
    merge inj@Inj{injChild = Pair child1 child2} = do
        childPattern <- termMerger child1 child2
        InjSimplifier{evaluateInj} <- askInjSimplifier
        let (childTerm, childCondition) = Pattern.splitTerm childPattern
            inj' = evaluateInj inj{injChild = childTerm}
        return $ Pattern.withCondition inj' childCondition

{- | Matches

@
\\equals{_, _}(inj{_,_}(_), f(_))
@

@
\\equals{_, _}(f(_), inj{_,_}(_))
@

and

@
\\and{_}(inj{_,_}(_), f(_))
@

@
\\and{_}(f(_), inj{_,_}(_))
@

when @f@ has the @constructor@ attribute.
-}
matchConstructorSortInjectionAndEquals ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe ()
matchConstructorSortInjectionAndEquals first second
    | Inj_ _ <- first
      , App_ symbol _ <- second
      , Symbol.isConstructor symbol =
        Just ()
    | Inj_ _ <- second
      , App_ symbol _ <- first
      , Symbol.isConstructor symbol =
        Just ()
    | otherwise = Nothing
{-# INLINE matchConstructorSortInjectionAndEquals #-}

{- | Unify a constructor application pattern with a sort injection pattern.

Sort injections clash with constructors, so @constructorSortInjectionAndEquals@
returns @\\bottom@.
-}
constructorSortInjectionAndEquals ::
    MonadUnify unifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    unifier a
constructorSortInjectionAndEquals first second =
    noConfusionInjectionConstructor first second

noConfusionInjectionConstructor ::
    MonadUnify unifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    unifier a
noConfusionInjectionConstructor term1 term2 =
    debugUnifyBottomAndReturnBottom
        "No confusion: sort injections and constructors"
        term1
        term2

{- |
 If the two constructors form an overload pair, apply the overloading axioms
 on the terms to make the constructors equal, then retry unification on them.

See <https://github.com/kframework/kore/blob/master/docs/2019-08-27-Unification-modulo-overloaded-constructors.md>
-}
overloadedConstructorSortInjectionAndEquals ::
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MaybeT unifier (Pattern RewritingVariableName)
overloadedConstructorSortInjectionAndEquals termMerger firstTerm secondTerm =
    do
        eunifier <-
            lift . Error.runExceptT $
                unifyOverloading (Pair firstTerm secondTerm)
        case eunifier of
            Right (Simple (Pair firstTerm' secondTerm')) ->
                lift $
                    termMerger firstTerm' secondTerm'
            Right
                ( WithNarrowing
                        Narrowing
                            { narrowingSubst
                            , narrowingVars
                            , overloadPair = Pair firstTerm' secondTerm'
                            }
                    ) -> do
                    boundPattern <- lift $ do
                        merged <- termMerger firstTerm' secondTerm'
                        Exists.makeEvaluate SideCondition.topTODO narrowingVars $
                            merged `Pattern.andCondition` narrowingSubst
                    case OrPattern.toPatterns boundPattern of
                        [result] -> return result
                        [] ->
                            lift $
                                debugUnifyBottomAndReturnBottom
                                    ( "exists simplification for overloaded"
                                        <> " constructors returned no pattern"
                                    )
                                    firstTerm
                                    secondTerm
                        _ -> empty
            Left (Clash message) ->
                lift $
                    debugUnifyBottomAndReturnBottom
                        (fromString message)
                        firstTerm
                        secondTerm
            Left Overloading.NotApplicable -> empty

{- | Unifcation or equality for a domain value pattern vs a constructor
application.

This unification case throws an error because domain values may not occur in a
sort with constructors.
-}
domainValueAndConstructorErrors ::
    Monad unifier =>
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MaybeT unifier a
domainValueAndConstructorErrors
    term1@(DV_ _ _)
    term2@(App_ secondHead _)
        | Symbol.isConstructor secondHead =
            error
                ( unlines
                    [ "Cannot handle DomainValue and Constructor:"
                    , unparseToString term1
                    , unparseToString term2
                    ]
                )
domainValueAndConstructorErrors
    term1@(App_ firstHead _)
    term2@(DV_ _ _)
        | Symbol.isConstructor firstHead =
            error
                ( unlines
                    [ "Cannot handle Constructor and DomainValue:"
                    , unparseToString term1
                    , unparseToString term2
                    ]
                )
domainValueAndConstructorErrors _ _ = empty

data UnifyDomainValue = UnifyDomainValue
    { val1, val2 :: !(TermLike RewritingVariableName)
    }

{- | Matches

@
\\equals{_, _}(\\dv{s}(_), \\dv{s}(_))
@

and

@
\\and{_}(\\dv{s}(_), \\dv{s}(_))
@
-}
matchDomainValue ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyDomainValue
matchDomainValue first second
    | DV_ sort1 val1 <- first
      , DV_ sort2 val2 <- second
      , sort1 == sort2 =
        Just UnifyDomainValue{val1, val2}
    | otherwise = Nothing
{-# INLINE matchDomainValue #-}

{- | Unify two domain values.

The two patterns are assumed to be inequal; therefore this case always return
@\\bottom@.

See also: 'equalAndEquals'
-}

-- TODO (thomas.tuegel): This unification case assumes that \dv is injective,
-- but it is not.
unifyDomainValue ::
    forall unifier.
    MonadUnify unifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    UnifyDomainValue ->
    unifier (Pattern RewritingVariableName)
unifyDomainValue term1 term2 unifyData
    | val1 == val2 =
        return $ Pattern.fromTermLike term1
    | otherwise = cannotUnifyDomainValues term1 term2
  where
    UnifyDomainValue{val1, val2} = unifyData

cannotUnifyDistinctDomainValues :: Text
cannotUnifyDistinctDomainValues = "distinct domain values"

cannotUnifyDomainValues ::
    MonadUnify unifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    unifier a
cannotUnifyDomainValues term1 term2 =
    debugUnifyBottomAndReturnBottom cannotUnifyDistinctDomainValues term1 term2

-- | @UnifyStringLiteral@ represents unification of two string literals.
data UnifyStringLiteral = UnifyStringLiteral
    { txt1, txt2 :: !Text
    }

-- | Matches the unification problem @"txt1"@ with @"txt2"@.
matchStringLiteral ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyStringLiteral
matchStringLiteral first second
    | StringLiteral_ txt1 <- first
      , StringLiteral_ txt2 <- second =
        Just UnifyStringLiteral{txt1, txt2}
    | otherwise = Nothing
{-# INLINE matchStringLiteral #-}

-- | Finish solving the 'UnifyStringLiteral' problem.
unifyStringLiteral ::
    forall unifier.
    MonadUnify unifier =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    UnifyStringLiteral ->
    unifier (Pattern RewritingVariableName)
unifyStringLiteral term1 term2 unifyData
    | txt1 == txt2 = return $ Pattern.fromTermLike term1
    | otherwise =
        debugUnifyBottomAndReturnBottom "distinct string literals" term1 term2
  where
    UnifyStringLiteral{txt1, txt2} = unifyData

{- | Unify any two function patterns.

The function patterns are unified by creating an @\\equals@ predicate. If either
argument is constructor-like, that argument will be the resulting 'term';
otherwise, the lesser argument is the resulting 'term'. The term always appears
on the left-hand side of the @\\equals@ predicate, and the other argument
appears on the right-hand side.
-}
functionAnd ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe (Pattern RewritingVariableName)
functionAnd first second
    | isFunctionPattern first
      , isFunctionPattern second =
        makeEqualsPredicate first' second'
            & Predicate.markSimplified
            -- Ceil predicate not needed since first being
            -- bottom will make the entire term bottom. However,
            -- one must be careful to not just drop the term.
            & Condition.fromPredicate
            & Pattern.withCondition first' -- different for Equals
            & pure
    | otherwise = empty
  where
    (first', second') = minMaxBy compareForEquals first second

{- | Normal ordering for terms in @\equals(_, _)@.

The normal ordering is arbitrary, but important to avoid duplication.
-}
compareForEquals ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Ordering
compareForEquals first second
    | isConstructorLike first = LT
    | isConstructorLike second = GT
    | otherwise = compare first second
