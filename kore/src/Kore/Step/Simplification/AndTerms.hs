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
    --, matchDomainValueAndConstructorErrors1
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
import Data.Text
    ( Text
    )

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Endianness as Builtin.Endianness
import qualified Kore.Builtin.Int as Builtin.Int
import qualified Kore.Builtin.KEqual as Builtin.KEqual
import qualified Kore.Builtin.List as Builtin.List
import qualified Kore.Builtin.Map as Builtin.Map
import qualified Kore.Builtin.Set as Builtin.Set
import qualified Kore.Builtin.Signedness as Builtin.Signedness
import qualified Kore.Builtin.String as Builtin.String
import Kore.IndexedModule.MetadataTools
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
        tools <- Simplifier.askMetadataTools
        let
            maybeTermUnification
                :: MaybeT unifier (Pattern RewritingVariableName)
            maybeTermUnification =
                maybeTermAnd notSimplifier termUnificationWorker tools pat1 pat2
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
    -> SmtMetadataTools Attribute.Symbol
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
maybeTermEquals notSimplifier childTransformers tools first second
    --unifyInt
  | Just unifyData <- Builtin.Int.matchInt first second
        = Builtin.Int.unifyInt unifyData
    --unifyBool
  | Just unifyData <- Builtin.Bool.matchBools first second
        = Builtin.Bool.unifyBool first second unifyData
    --unifyString
  | Just unifyData <- Builtin.String.matchString first second
        = Builtin.String.unifyString first second unifyData
    --unifyDV
  | Just unifyData <- matchDomainValue first second
        = unifyDomainValue first second unifyData
    --unifySL
  | Just unifyData <- matchStringLiteral first second
        = unifyStringLiteral first second unifyData
    --equalsAndEquals
  | Just () <- matchEqualsAndEquals first second
        = equalAndEquals first
    --bytesDiff
  | Just () <- matchBytesDifferent first second
        = bytesDifferent
    --bottomTermEquals
  | Just () <- matchFirstBottom first
        = bottomTermEquals SideCondition.topTODO first second
    --termBottomEquals
  | Just () <- matchFirstBottom second
        = termBottomEquals SideCondition.topTODO first second
    --variableFuncEq x2
  | Just var <- matchVariableFunctionEquals first
        = variableFunctionEquals first second var
  | Just var <- matchVariableFunctionEquals second
        = variableFunctionEquals second first var
    --equalInjHeadsAndEquals
  | Just unifyData <- matchEqualInjectiveHeadsAndEquals first second
        = equalInjectiveHeadsAndEquals
            childTransformers
            unifyData
    --sortInjAndEquals
  | Just unifyData <- matchSortInjectionAndEquals first second
        = sortInjectionAndEquals childTransformers first second unifyData
    --constructorSortInjAndEq
  | Just () <- matchConstructorSortInjectionAndEquals first second
        = constructorSortInjectionAndEquals first second
  | Just () <- matchConstructorSortInjectionAndEquals second first
        = constructorSortInjectionAndEquals second first
    --constructorAndEqualsAssumesDiffHeads
  | Just unifyData <- matchConstructorAndEqualsAssumesDifferentHeads first second
        = constructorAndEqualsAssumesDifferentHeads first second unifyData
    --overloadedConstructorSortInjAndEq
  | Just unifyData <- matchOverloadedConstructorSortInjectionAndEquals first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second
            unifyData
    --unifyBoolAnd
  | Just boolAnd <- Builtin.Bool.matchUnifyBoolAnd first second
        = Builtin.Bool.unifyBoolAnd childTransformers first boolAnd
  | Just boolAnd <- Builtin.Bool.matchUnifyBoolAnd second first
        = Builtin.Bool.unifyBoolAnd childTransformers second boolAnd
    --unifyBoolOr
  | Just boolOr <- Builtin.Bool.matchUnifyBoolOr first second
        = Builtin.Bool.unifyBoolOr childTransformers first boolOr
  | Just boolOr <- Builtin.Bool.matchUnifyBoolOr second first
        = Builtin.Bool.unifyBoolOr childTransformers second boolOr
    --unifyBoolNot
  | Just unifyData <- Builtin.Bool.matchUnifyBoolNot first second
        = Builtin.Bool.unifyBoolNot childTransformers first unifyData
  | Just unifyData <- Builtin.Bool.matchUnifyBoolNot second first
        = Builtin.Bool.unifyBoolNot childTransformers second unifyData
    --unifyIntEq
  | Just eqTerm <- Builtin.Int.matchUnifyIntEq first second
        = --Builtin.EqTerm.unifyEqTerm childTransformers notSimplifier eqTerm otherTerm  -- TODO: fix this
            Builtin.Int.unifyIntEq childTransformers notSimplifier second eqTerm
  | Just eqTerm <- Builtin.Int.matchUnifyIntEq second first -- TODO: fix this
        = Builtin.Int.unifyIntEq childTransformers notSimplifier first eqTerm
    --unifyStringEq
  | Just eqTerm <- Builtin.String.matchUnifyStringEq first second
        = Builtin.String.unifyStringEq childTransformers notSimplifier second eqTerm -- TODO: fix this
  | Just eqTerm <- Builtin.String.matchUnifyStringEq second first -- TODO: fix this
        = Builtin.String.unifyStringEq childTransformers notSimplifier first eqTerm
    --unifyKEqualsK
  | Just eqTerm <- Builtin.KEqual.matchUnifyKequalsEq first
        = Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier second eqTerm
  | Just eqTerm <- Builtin.KEqual.matchUnifyKequalsEq second
        = Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier first eqTerm
    --unifyEquals endian
  | Just unifyData <- Builtin.Endianness.matchUnifyEqualsEndianness first second
        = Builtin.Endianness.unifyEquals first second unifyData
    --unifyEquals signedness
  | Just unifyData <- Builtin.Signedness.matchUnifyEqualsSignedness first second
        = Builtin.Signedness.unifyEquals first second unifyData
    --unifyEquals map
  | Just unifyData <- Builtin.Map.matchUnifyEqualsMap tools first second
        = Builtin.Map.unifyEquals tools childTransformers first second unifyData
    --unifyNotInKeys
  | Just unifyData <- Builtin.Map.matchUnifyNotInKeys first
        = Builtin.Map.unifyNotInKeys childTransformers notSimplifier first unifyData
  | Just unifyData <- Builtin.Map.matchUnifyNotInKeys second
        = Builtin.Map.unifyNotInKeys childTransformers notSimplifier second unifyData
    --unifyEquals set
  | Just unifyData <- Builtin.Set.matchUnifyEqualsSet tools first second
        = Builtin.Set.unifyEquals tools childTransformers first second unifyData
    --unifyEquals list
  | Just unifyData <- Builtin.List.matchUnifyEqualsList first' second'
        = Builtin.List.unifyEquals SimplificationType.Equals childTransformers first' second' unifyData
    --dVACE
  | Just () <- matchDomainValueAndConstructorErrors first second
        = domainValueAndConstructorErrors1 first second
  | Just () <- matchDomainValueAndConstructorErrors second first
        = domainValueAndConstructorErrors2 second first
  | otherwise = empty

    where
        first' = Builtin.List.normalize first
        second' = Builtin.List.normalize second

maybeTermAnd
    :: MonadUnify unifier
    => HasCallStack
    => NotSimplifier unifier
    -> TermSimplifier RewritingVariableName unifier
    -- ^ Used to simplify subterm "and".
    -> SmtMetadataTools Attribute.Symbol
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
maybeTermAnd notSimplifier childTransformers tools first second
    --expandAlias
  | Just unifyData <- matchExpandAlias first second
        = let UnifyExpandAlias { term1, term2 } = unifyData in
            maybeTermAnd
                notSimplifier
                childTransformers
                tools
                term1
                term2
    --boolAnd
  | Just unifyData <- matchBoolAnd first
        = unifyBoolAnd first second unifyData
  | Just unifyData <- matchBoolAnd second
        = unifyBoolAnd second first unifyData
    --unifyInt
  | Just unifyData <- Builtin.Int.matchInt first second
        = Builtin.Int.unifyInt unifyData
    --unifyBool
  | Just unifyData <- Builtin.Bool.matchBools first second
        = Builtin.Bool.unifyBool first second unifyData
    --unifyString
  | Just unifyData <- Builtin.String.matchString first second
        = Builtin.String.unifyString first second unifyData
    --unifyDV
  | Just unifyData <- matchDomainValue first second
        = unifyDomainValue first second unifyData
    --unifyStringLit
  | Just unifyData <- matchStringLiteral first second
        = unifyStringLiteral first second unifyData
    --equalAndEq
  | Just () <- matchEqualsAndEquals first second
        = equalAndEquals first
    --bytesDiff
  | Just () <- matchBytesDifferent first second
        = bytesDifferent
    --variableFunAnd x2
  | Just unifyData <- matchVariableFunctionAnd first second
        = variableFunctionAnd second unifyData
  | Just unifyData <- matchVariableFunctionAnd second first
        = variableFunctionAnd first unifyData
    -- equalInjHeadsAndEq
  | Just unifyData <- matchEqualInjectiveHeadsAndEquals first second
        = equalInjectiveHeadsAndEquals
            childTransformers
            unifyData
    -- sortInjAndEq
  | Just unifyData <- matchSortInjectionAndEquals first second
        = sortInjectionAndEquals childTransformers first second unifyData
    -- constructorSortInj
  | Just () <- matchConstructorSortInjectionAndEquals first second
        = constructorSortInjectionAndEquals first second 
  | Just () <- matchConstructorSortInjectionAndEquals second first
        = constructorSortInjectionAndEquals second first
    -- constructorAndEqualsAssumes...
  | Just unifyData <- matchConstructorAndEqualsAssumesDifferentHeads first second
        = constructorAndEqualsAssumesDifferentHeads first second unifyData
    -- overloadedConstructor...
  | Just unifyData <- matchOverloadedConstructorSortInjectionAndEquals first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second
            unifyData
    --unifyBoolAnd
  | Just boolAnd <- Builtin.Bool.matchUnifyBoolAnd first second
        = Builtin.Bool.unifyBoolAnd childTransformers first boolAnd
  | Just boolAnd <- Builtin.Bool.matchUnifyBoolAnd second first
        = Builtin.Bool.unifyBoolAnd childTransformers second boolAnd
    --unifyBoolOr
  | Just boolOr <- Builtin.Bool.matchUnifyBoolOr first second
        = Builtin.Bool.unifyBoolOr childTransformers first boolOr
  | Just boolOr <- Builtin.Bool.matchUnifyBoolOr second first
        = Builtin.Bool.unifyBoolOr childTransformers second boolOr
    --unifyBoolNot
  | Just unifyData <- Builtin.Bool.matchUnifyBoolNot first second
        = Builtin.Bool.unifyBoolNot childTransformers first unifyData
    --unifyKEqualsEq
  | Just eqTerm <- Builtin.KEqual.matchUnifyKequalsEq first
        = Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier second eqTerm
  | Just eqTerm <- Builtin.KEqual.matchUnifyKequalsEq second
        = Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier first eqTerm
    --unifyITE
  | Just ifThenElse <- Builtin.KEqual.matchIfThenElse first
        = Builtin.KEqual.unifyIfThenElse childTransformers ifThenElse second
  | Just ifThenElse <- Builtin.KEqual.matchIfThenElse second
        = Builtin.KEqual.unifyIfThenElse childTransformers ifThenElse first
    --unifyEquals endianness
  | Just unifyData <- Builtin.Endianness.matchUnifyEqualsEndianness first second
        = Builtin.Endianness.unifyEquals first second unifyData
   --unifyEquals signedness
  | Just unifyData <- Builtin.Signedness.matchUnifyEqualsSignedness first second
        = Builtin.Signedness.unifyEquals first second unifyData
    --unifyEquals map
  | Just unifyData <- Builtin.Map.matchUnifyEqualsMap tools first second
        = Builtin.Map.unifyEquals tools childTransformers first second unifyData
    --unifyEquals set
  | Just unifyData <- Builtin.Set.matchUnifyEqualsSet tools first second
        = Builtin.Set.unifyEquals tools childTransformers first second unifyData
    --unifyEqualsList
  | Just unifyData <- Builtin.List.matchUnifyEqualsList first' second'
        = Builtin.List.unifyEquals SimplificationType.Equals childTransformers first' second' unifyData
        --domainValue...
  | Just () <- matchDomainValueAndConstructorErrors first second
        = domainValueAndConstructorErrors1 first second
  | Just () <- matchDomainValueAndConstructorErrors second first
        = domainValueAndConstructorErrors2 first second
        --functionAnd
  | Just () <- matchFunctionAnd first second
        = Error.hoistMaybe (functionAnd first second)
  | otherwise = empty

    where
        first' = Builtin.List.normalize first
        second' = Builtin.List.normalize second

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

-- -- | Simplify the conjunction of terms where one is a predicate.
-- boolAnd
--     :: MonadUnify unifier
--     => TermLike RewritingVariableName
--     -> TermLike RewritingVariableName
--     -> MaybeT unifier (Pattern RewritingVariableName)
-- boolAnd first second
--   | isBottom first  = do
--       explainBoolAndBottom first second
--       return (Pattern.fromTermLike first)
--   | isTop first     = return (Pattern.fromTermLike second)
--   | isBottom second = do
--       explainBoolAndBottom first second
--       return (Pattern.fromTermLike second)
--   | isTop second    = return (Pattern.fromTermLike first)
--   | otherwise       = empty

explainBoolAndBottom
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier ()
explainBoolAndBottom term1 term2 =
    lift $ explainBottom "Cannot unify bottom." term1 term2

matchEqualsAndEquals
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe ()
matchEqualsAndEquals first second
    | first == second
        = Just ()
    | otherwise = Nothing
{-# INLINE matchEqualsAndEquals #-}

-- | Unify two identical ('==') patterns.
equalAndEquals
    :: Monad unifier
    => TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
equalAndEquals first =
    return (Pattern.fromTermLike first)
    -- TODO: fix name

matchFirstBottom
    :: TermLike RewritingVariableName
    -> Maybe ()
matchFirstBottom first
    | Bottom_ _ <- first
        = Just ()
    | otherwise = Nothing
{-# INLINE matchFirstBottom #-}

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals
    :: MonadUnify unifier
    => SideCondition RewritingVariableName
    -> TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
bottomTermEquals
    sideCondition
    first
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

data VariableFunctionAnd
    = VariableFunctionAnd1 (ElementVariable RewritingVariableName)
    | VariableFunctionAnd2 (ElementVariable RewritingVariableName)

matchVariableFunctionAnd
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe VariableFunctionAnd
matchVariableFunctionAnd first second
    | ElemVar_ v <- first
    , ElemVar_ _ <- second
    = Just $ VariableFunctionAnd1 v
    | ElemVar_ v <- first
    , isFunctionPattern second
    = Just $ VariableFunctionAnd2 v
    | otherwise
    = Nothing

variableFunctionAnd
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> VariableFunctionAnd
    -> MaybeT unifier (Pattern RewritingVariableName)
variableFunctionAnd term unifyData
    = case unifyData of
        VariableFunctionAnd1 v ->
            return $ Pattern.assign (inject v) term
        VariableFunctionAnd2 v ->
            lift $ return (Pattern.withCondition term result)
          where
            result = Condition.fromSingleSubstitution
                (Substitution.assign (inject v) term)

matchVariableFunctionEquals
    :: TermLike RewritingVariableName
    -> Maybe (ElementVariable RewritingVariableName)
matchVariableFunctionEquals first
    | ElemVar_ var <- first
        = Just var
    | otherwise = Nothing
{-# INLINE matchVariableFunctionEquals #-}


{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

 -}
variableFunctionEquals
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> ElementVariable RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
variableFunctionEquals
    first
    second
    v
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
  | otherwise = empty

data SortInjectionAndEquals = SortInjectionAndEquals {
    inj1, inj2 :: Inj (TermLike RewritingVariableName)
}

matchSortInjectionAndEquals
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe SortInjectionAndEquals
matchSortInjectionAndEquals first second
    | Inj_ inj1 <- first
    , Inj_ inj2 <- second
        = Just $ SortInjectionAndEquals inj1 inj2
    | otherwise = Nothing
{-# INLINE sortInjectionAndEquals #-}

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
    -> SortInjectionAndEquals
    -> MaybeT unifier (Pattern RewritingVariableName)
sortInjectionAndEquals termMerger first second unifyData = do
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

    SortInjectionAndEquals { inj1, inj2 } = unifyData

matchConstructorSortInjectionAndEquals
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe ()
matchConstructorSortInjectionAndEquals first second
    | Inj_ _ <- first
    , App_ symbol _ <- second
    , Symbol.isConstructor symbol
        = Just ()
    | otherwise = Nothing
{-# INLINE matchConstructorSortInjectionAndEquals #-}

{- | Unify a constructor application pattern with a sort injection pattern.

Sort injections clash with constructors, so @constructorSortInjectionAndEquals@
returns @\\bottom@.

 -}
constructorSortInjectionAndEquals
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier a
constructorSortInjectionAndEquals first second
    = lift $ noConfusionInjectionConstructor first second

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
    -> OverloadedConstructorSortInjectionAndEquals
    -> MaybeT unifier (Pattern RewritingVariableName)
overloadedConstructorSortInjectionAndEquals termMerger firstTerm secondTerm unifyData
  = do
    eunifier <- lift . Error.runExceptT $ getUnifyResult firstTerm secondTerm unifyData
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

matchDomainValueAndConstructorErrors
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe ()
matchDomainValueAndConstructorErrors first second
    | DV_ _ _ <- first
    , App_ secondHead _ <- second
    , Symbol.isConstructor secondHead
    = Just ()
    | otherwise = Nothing

domainValueAndConstructorErrors1
    :: HasCallStack
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier a
domainValueAndConstructorErrors1
    term1 term2 =
      error (unlines [ "Cannot handle DomainValue and Constructor:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )

domainValueAndConstructorErrors2
    :: HasCallStack
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier a
domainValueAndConstructorErrors2
    term1 term2 =
      error (unlines [ "Cannot handle Constructor and DomainValue:"
                     , unparseToString term1
                     , unparseToString term2
                     ]
            )

data UnifyDomainValue = UnifyDomainValue {
    sort1 :: Sort
    , val1 :: TermLike RewritingVariableName
    , sort2 :: Sort
    , val2 :: TermLike RewritingVariableName
}

matchDomainValue
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe UnifyDomainValue
matchDomainValue first second
    | DV_ sort1 val1 <- first
    , DV_ sort2 val2 <- second
        = Just $ UnifyDomainValue sort1 val1 sort2 val2
    | otherwise = Nothing
{-# INLINE matchDomainValue #-}

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
    -> UnifyDomainValue
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyDomainValue term1 term2 unifyData =
    assert (sort1 == sort2) $ lift worker
  where
    worker :: unifier (Pattern RewritingVariableName)
    worker
      | val1 == val2 =
        return $ Pattern.fromTermLike term1
      | otherwise = cannotUnifyDomainValues term1 term2

    UnifyDomainValue { sort1, val1, sort2, val2 } = unifyData

cannotUnifyDistinctDomainValues :: Pretty.Doc ()
cannotUnifyDistinctDomainValues = "distinct domain values"

cannotUnifyDomainValues
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> unifier a
cannotUnifyDomainValues = explainAndReturnBottom cannotUnifyDistinctDomainValues

data UnifyStringLiteral = UnifyStringLiteral {
    txt1, txt2 :: Text
}

matchStringLiteral
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe UnifyStringLiteral
matchStringLiteral first second
    | StringLiteral_ string1 <- first
    , StringLiteral_ string2 <- second
        = Just $ UnifyStringLiteral string1 string2
    | otherwise = Nothing
{-# INLINE matchStringLiteral #-}

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
    -> UnifyStringLiteral
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyStringLiteral term1 term2 unifyData = lift worker
  where
    worker :: unifier (Pattern RewritingVariableName)
    worker
      | txt1 == txt2 =
        return $ Pattern.fromTermLike term1
      | otherwise = explainAndReturnBottom "distinct string literals" term1 term2

    UnifyStringLiteral { txt1, txt2 } = unifyData

matchFunctionAnd
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe ()
matchFunctionAnd first second
    | isFunctionPattern first
    , isFunctionPattern second
    = Just ()
    | otherwise
    = Nothing

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
functionAnd first second =
    makeEqualsPredicate first' second'
    & Predicate.markSimplified
    -- Ceil predicate not needed since first being
    -- bottom will make the entire term bottom. However,
    -- one must be careful to not just drop the term.
    & Condition.fromPredicate
    & Pattern.withCondition first'  -- different for Equals
    & pure
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



matchBytesDifferent
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe ()
matchBytesDifferent first second
    | _ :< InternalBytesF (Const bytesFirst) <- Recursive.project first
    , _ :< InternalBytesF (Const bytesSecond) <- Recursive.project second
    , bytesFirst /= bytesSecond 
        =  Just ()
    | otherwise = Nothing
{-# INLINE matchBytesDifferent #-}

bytesDifferent
    :: MonadUnify unifier
    => MaybeT unifier (Pattern RewritingVariableName)
bytesDifferent = return Pattern.bottom

data UnifyExpandAlias = UnifyExpandAlias {
    term1, term2 :: !(TermLike RewritingVariableName)
}

matchExpandAlias
    :: TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Maybe UnifyExpandAlias
matchExpandAlias first second
    | Just term1 <- expandSingleAlias first
    , Just term2 <- expandSingleAlias second
    = Just $ UnifyExpandAlias term1 term2
    | otherwise
    = Nothing

data UnifyBoolAnd
    = UnifyBoolAndBottom
    | UnifyBoolAndTop

matchBoolAnd
    :: TermLike RewritingVariableName
    -> Maybe UnifyBoolAnd
matchBoolAnd term
    | Pattern.isBottom term
    = Just UnifyBoolAndBottom
    | Pattern.isTop term
    = Just UnifyBoolAndTop
    | otherwise
    = Nothing

unifyBoolAnd
    :: forall unifier
    .  MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> UnifyBoolAnd
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyBoolAnd first second unifyData
    = case unifyData of
        UnifyBoolAndBottom ->
            explainBoolAndBottom first second
            >> return (Pattern.fromTermLike first)
        UnifyBoolAndTop ->
            return $ Pattern.fromTermLike first

--     --boolAnd
--   | Just UnifyBoolAnd1 <- matchBoolAnd1 first
--         = explainBoolAndBottom first second
--           >> return (Pattern.fromTermLike first)
--   | Just UnifyBoolAnd2 <- matchBoolAnd2 first
--         = return $ Pattern.fromTermLike second
--   | Just UnifyBoolAnd3 <- matchBoolAnd3 first
--         = explainBoolAndBottom first second
--           >> return (Pattern.fromTermLike second)
--   | Just UnifyBoolAnd4 <- matchBoolAnd4 first
--         = return $ Pattern.fromTermLike first