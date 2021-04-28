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
import Data.String
    ( fromString
    )
import Data.Text
    ( Text
    )

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Endianness as Builtin.Endianness
--import qualified Kore.Builtin.EqTerm as Builtin.EqTerm
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
import Kore.Step.Simplification.InjSimplifier
import Kore.Step.Simplification.NoConfusion
import Kore.Step.Simplification.NotSimplifier
import Kore.Step.Simplification.Overloading as Overloading
import qualified Kore.Step.Simplification.SimplificationType as SimplificationType
    ( SimplificationType (..)
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Simplification.Unify
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
  | Just (UnifyInt int1 int2) <- matchInt first second
        = Builtin.Int.unifyInt int1 int2
    --unifyBool
  | Just (UnifyBool bool1 bool2) <- matchBools first second
        = Builtin.Bool.unifyBool bool1 bool2
    --unifyString
  | Just (UnifyString string1 string2) <- matchString first second
        = Builtin.String.unifyString string1 string2
    --unifyDV
  | Just (UnifyDomainValue sort1 val1 sort2 val2) <- matchDomainValue first second
        = unifyDomainValue sort1 val1 sort2 val2
    --unifySL
  | Just (UnifyStringLiteral txt1 txt2) <- matchStringLiteral first second
        = unifyStringLiteral txt1 txt2
    --equalsAndEquals
  | Just EqualsAndEquals <- matchUnDefined first second
        = equalAndEquals first
    --bytesDiff
  | Just (BytesDifferent bytes1 bytes2) <- matchBytesDifferent first second
        = bytesDifferent bytes1 bytes2
    --bottomTermEquals
  | Just (UnifyFirstBottom sort) <- matchFirstBottom first
        = bottomTermEquals SideCondition.topTODO sort second
    --termBottomEquals
  | Just (UnifyFirstBottom sort) <- matchFirstBottom second
        = termBottomEquals SideCondition.topTODO first sort
    --variableFuncEq x2
  | Just (VariableFunctionEquals var) <- matchFirstElemVar first
        = variableFunctionEquals var second
  | Just (VariableFunctionEquals var) <- matchFirstElemVar second
        = variableFunctionEquals var first
    --equalInjHeadsAndEquals
  | Just (EqualInjectiveHeadsAndEquals
            firstHead
            firstChildren
            secondHead
            secondChildren) <- matchEqualInjectiveHeadsAndEquals first second
        = equalInjectiveHeadsAndEquals
            childTransformers
            firstHead
            firstChildren
            secondHead
            secondChildren
    --sortInjAndEquals
  | Just (MatchInjs inj1 inj2) <- matchInjs first second
        = sortInjectionAndEquals childTransformers inj1 inj2
    --constructorSortInjAndEq
  | Just (MatchInjApp symbol) <- matchInjApp first second
        = constructorSortInjectionAndEquals first second symbol
  | Just (MatchAppInj symbol) <- matchAppInj first second
        = constructorSortInjectionAndEquals second first symbol
    --constructorAndEqualsAssumesDiffHeads
  | Just (MatchAppHeads symbol1 symbol2) <- matchAppHeads first second
        = constructorAndEqualsAssumesDifferentHeads first second symbol1 symbol2
    --overloadedConstructorSortInjAndEq
  | Just (UnifyOverload1 (UnifyOverload1Args firstHead secondHead firstChildren inj)) <- matchUnifyOverload1 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading1
                    firstHead
                    firstChildren
                    secondHead
                    second
                    inj
  | Just (UnifyOverload2 (UnifyOverload2Args firstHead secondHead secondChildren inj)) <- matchUnifyOverload2 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading2
                    firstHead
                    first
                    secondHead
                    secondChildren
                    inj
  | Just (UnifyOverload3 (UnifyOverload3Args firstHead secondHead firstChildren secondChildren inj)) <- matchUnifyOverload3 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading3
                    firstHead
                    firstChildren
                    secondHead
                    secondChildren
                    inj
  | Just (UnifyOverload4 (UnifyOverload4Args firstHead secondVar inj)) <- matchUnifyOverload4 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading4
                    first
                    firstHead
                    secondVar
                    inj
  | Just (UnifyOverload5 (UnifyOverload5Args firstTerm firstHead firstChildren secondVar inj)) <- matchUnifyOverload5 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading5
                    firstTerm
                    firstHead
                    firstChildren
                    secondVar
                    inj

  | Just (UnifyOverload6 (UnifyOverload6Args firstHead injChild)) <- matchUnifyOverload6 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading6 firstHead injChild
    --unifyBoolAnd
  | Just (UnifyBoolAnd term1 term2) <- matchUnifyBoolAnd1 first second
        = Builtin.Bool.unifyBoolAnd childTransformers first second term1 term2
  | Just (UnifyBoolAnd term1 term2) <- matchUnifyBoolAnd2 first second
        = Builtin.Bool.unifyBoolAnd childTransformers second first term1 term2
    --unifyBoolOr
  | Just (UnifyBoolOr (UnifyBoolOrArgs term operand1 operand2)) <- matchUnifyBoolOr1 first second
        = Builtin.Bool.unifyBoolOr childTransformers term operand1 operand2
  | Just (UnifyBoolOr (UnifyBoolOrArgs term operand1 operand2)) <- matchUnifyBoolOr2 first second
        = Builtin.Bool.unifyBoolOr childTransformers term operand1 operand2
    --unifyBoolNot
  | Just (UnifyBoolNot (UnifyBoolNotArgs term operand value)) <- matchUnifyBoolNot first second
        = Builtin.Bool.unifyBoolNot childTransformers term operand value
    --unifyIntEq
  | Just (UnifyIntEq (UnifyIntEqArgs _ _ {-eqTerm otherTerm-})) <- matchUnifyIntEq first second
        = --Builtin.EqTerm.unifyEqTerm childTransformers notSimplifier eqTerm otherTerm  -- TODO: fix this
            Builtin.Int.unifyIntEq childTransformers notSimplifier first second
  | Just (UnifyIntEq (UnifyIntEqArgs _ _ )) <- matchUnifyIntEq second first -- TODO: fix this
        = Builtin.Int.unifyIntEq childTransformers notSimplifier second first
    --unifyStringEq
  | Just (UnifyStringEq (UnifyStringEqArgs _ _ {-eqTerm otherTerm-})) <- matchUnifyStringEq first second
        = Builtin.String.unifyStringEq childTransformers notSimplifier first second -- TODO: fix this
  | Just (UnifyStringEq (UnifyStringEqArgs _ _)) <- matchUnifyStringEq second first -- TODO: fix this
        = Builtin.String.unifyStringEq childTransformers notSimplifier second first
    --unifyKEqualsK
  | Just (UnifyKequalsEq (UnifyKequalsEqArgs eqTerm otherTerm)) <- matchUnifyKequalsEq first second
        = Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier eqTerm otherTerm
    --unifyEquals endian
  | Just (UnifyEqualsEndianness (UnifyEqualsEndiannessArgs end1 end2)) <- matchUnifyEqualsEndianness first second
        = Builtin.Endianness.unifyEquals first second end1 end2
    --unifyEquals signedness
  | Just (UnifyEqualsSignedness (UnifyEqualsSignednessArgs sign1 sign2)) <- matchUnifyEqualsSignedness first second
        = Builtin.Signedness.unifyEquals first second sign1 sign2
    --unifyEquals map
  | Just (UnifyEqualsMap1 (UnifyMapEqualsArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2)) <- matchUnifyEqualsMap tools first second
        = Builtin.Map.unifyEquals1 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2
  | Just (UnifyEqualsMap2 (UnifyMapEqualsVarArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var)) <- matchUnifyEqualsMap tools first second
        = Builtin.Map.unifyEquals2 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var
  | Just (UnifyEqualsMap3 (UnifyMapEqualsVarArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var)) <- matchUnifyEqualsMap tools first second
        = Builtin.Map.unifyEquals3 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var
  | Just UnifyMapBottom <- matchUnifyEqualsMap tools first second
        = lift $ Unify.explainAndReturnBottom
            "Duplicated elements in normalization." first second
    --unifyNotInKeys
  | Just (UnifyNotInKeys (UnifyNotInKeysArgs inKeys term keyTerm mapTerm)) <- matchUnifyNotInKeys first second
        = Builtin.Map.unifyNotInKeys childTransformers notSimplifier term inKeys keyTerm mapTerm
    --unifyEquals set
  | Just (UnifyEqualsSet1 (UnifySetEqualsArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2)) <- matchUnifyEqualsSet tools first second
        = Builtin.Set.unifyEquals1 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2
  | Just (UnifyEqualsSet2 (UnifySetEqualsVarArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var)) <- matchUnifyEqualsSet tools first second
        = Builtin.Set.unifyEquals2 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var
  | Just (UnifyEqualsSet3 (UnifySetEqualsVarArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var)) <- matchUnifyEqualsSet tools first second
        = Builtin.Set.unifyEquals3 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var
  | Just UnifySetBottom <- matchUnifyEqualsSet tools first second
        = lift $ Unify.explainAndReturnBottom
            "Duplicated elements in normalization." first second
    --unifyEquals list
  | Just UnifyEqualsList1 <- matchUnifyEqualsList (Builtin.List.normalize first) (Builtin.List.normalize second)
        = Builtin.List.unify1 childTransformers first second
  | Just UnifyEqualsList2 <- matchUnifyEqualsList (Builtin.List.normalize first) (Builtin.List.normalize second)
        = Builtin.List.unify2 childTransformers first second
  | Just (UnifyEqualsList3 (UnifyEqualsList3Args symbol2 args1 args2)) <- matchUnifyEqualsList (Builtin.List.normalize first) (Builtin.List.normalize second)
        = Builtin.List.unify3 childTransformers first second symbol2 args1 args2
  | Just (UnifyEqualsList4 (UnifyEqualsList4Args builtin1 builtin2)) <- matchUnifyEqualsList (Builtin.List.normalize first) (Builtin.List.normalize second)
        = Builtin.List.unify4 childTransformers first second builtin1 builtin2
  | Just (UnifyEqualsList5 (UnifyEqualsList5Args builtin args)) <- matchUnifyEqualsList (Builtin.List.normalize first) (Builtin.List.normalize second)
        = Builtin.List.unify5 SimplificationType.Equals childTransformers first second args builtin
    --dVACE
  | Just DomainValueAndConstructorErrors1 <- matchDomainValueAndConstructorErrors1 first second
        = domainValueAndConstructorErrors1 first second
  | Just DomainValueAndConstructorErrors2 <- matchDomainValueAndConstructorErrors2 first second
        = domainValueAndConstructorErrors2 first second
  | otherwise = empty

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
  | Just (UnifyExpandAlias (UnifyExpandAliasArgs term1 term2)) <- matchExpandAlias first second
        = maybeTermAnd
            notSimplifier
            childTransformers
            tools
            term1
            term2
    --boolAnd
  | Just UnifyBoolAnd1 <- matchBoolAnd1 first
        = explainBoolAndBottom first second
          >> return (Pattern.fromTermLike first)
  | Just UnifyBoolAnd2 <- matchBoolAnd2 first
        = return $ Pattern.fromTermLike second
  | Just UnifyBoolAnd3 <- matchBoolAnd3 first
        = explainBoolAndBottom first second
          >> return (Pattern.fromTermLike second)
  | Just UnifyBoolAnd4 <- matchBoolAnd4 first
        = return $ Pattern.fromTermLike first
    --unifyInt
  | Just (UnifyInt int1 int2) <- matchInt first second
        = Builtin.Int.unifyInt int1 int2
    --unifyBool
  | Just (UnifyBool bool1 bool2) <- matchBools first second
        = Builtin.Bool.unifyBool bool1 bool2
    --unifyString
  | Just (UnifyString string1 string2) <- matchString first second
        = Builtin.String.unifyString string1 string2
    --unifyDV
  | Just (UnifyDomainValue sort1 val1 sort2 val2) <- matchDomainValue first second
        = unifyDomainValue sort1 val1 sort2 val2
    --unifyStringLit
  | Just (UnifyStringLiteral txt1 txt2) <- matchStringLiteral first second
        = unifyStringLiteral txt1 txt2
    --equalAndEq
  | Just EqualsAndEquals <- matchUnDefined first second
        = equalAndEquals first
    --bytesDiff
  | Just (BytesDifferent bytes1 bytes2) <- matchBytesDifferent first second
        = bytesDifferent bytes1 bytes2
    --variableFunAnd x2
  | Just (UnifyVariableFunctionAnd1 v) <- matchVariableFunctionAnd1 first second
        = variableFunctionAnd1 v second
  | Just (UnifyVariableFunctionAnd2 v) <- matchVariableFunctionAnd2 first second
        = variableFunctionAnd2 v second
  | Just (UnifyVariableFunctionAnd1 v) <- matchVariableFunctionAnd1 second first
        = variableFunctionAnd1 v first
  | Just (UnifyVariableFunctionAnd2 v) <- matchVariableFunctionAnd2 second first
        = variableFunctionAnd2 v first
    -- equalInjHeadsAndEq
  | Just (EqualInjectiveHeadsAndEquals
            firstHead
            firstChildren
            secondHead
            secondChildren) <- matchEqualInjectiveHeadsAndEquals first second
        = equalInjectiveHeadsAndEquals
            childTransformers
            firstHead
            firstChildren
            secondHead
            secondChildren
    -- sortInjAndEq
  | Just (MatchInjs inj1 inj2) <- matchInjs first second
        = sortInjectionAndEquals childTransformers inj1 inj2
    -- constructorSortInj
  | Just (MatchInjApp symbol) <- matchInjApp first second
        = constructorSortInjectionAndEquals first second symbol
  | Just (MatchAppInj symbol) <- matchAppInj first second
        = constructorSortInjectionAndEquals second first symbol
    -- constructorAndEqualsAssumes...
  | Just (MatchAppHeads symbol1 symbol2) <- matchAppHeads first second
        = constructorAndEqualsAssumesDifferentHeads first second symbol1 symbol2
    -- overloadedConstructor...
  | Just (UnifyOverload1 (UnifyOverload1Args firstHead secondHead firstChildren inj)) <- matchUnifyOverload1 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading1
                    firstHead
                    firstChildren
                    secondHead
                    second
                    inj
  | Just (UnifyOverload2 (UnifyOverload2Args firstHead secondHead secondChildren inj)) <- matchUnifyOverload2 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading2
                    firstHead
                    first
                    secondHead
                    secondChildren
                    inj
  | Just (UnifyOverload3 (UnifyOverload3Args firstHead secondHead firstChildren secondChildren inj)) <- matchUnifyOverload3 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading3
                    firstHead
                    firstChildren
                    secondHead
                    secondChildren
                    inj
  | Just (UnifyOverload4 (UnifyOverload4Args firstHead secondVar inj)) <- matchUnifyOverload4 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading4
                    first
                    firstHead
                    secondVar
                    inj
  | Just (UnifyOverload5 (UnifyOverload5Args firstTerm firstHead firstChildren secondVar inj)) <- matchUnifyOverload5 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading5
                    firstTerm
                    firstHead
                    firstChildren
                    secondVar
                    inj

  | Just (UnifyOverload6 (UnifyOverload6Args firstHead injChild)) <- matchUnifyOverload6 first second
        = overloadedConstructorSortInjectionAndEquals
            childTransformers
            first
            second $
                Overloading.unifyOverloading6 firstHead injChild
    --unifyBoolAnd
  | Just (UnifyBoolAnd term1 term2) <- matchUnifyBoolAnd1 first second
        = Builtin.Bool.unifyBoolAnd childTransformers first second term1 term2
  | Just (UnifyBoolAnd term1 term2) <- matchUnifyBoolAnd2 first second
        = Builtin.Bool.unifyBoolAnd childTransformers second first term1 term2
    --unifyBoolOr
  | Just (UnifyBoolOr (UnifyBoolOrArgs term operand1 operand2)) <- matchUnifyBoolOr1 first second
        = Builtin.Bool.unifyBoolOr childTransformers term operand1 operand2
  | Just (UnifyBoolOr (UnifyBoolOrArgs term operand1 operand2)) <- matchUnifyBoolOr2 first second
        = Builtin.Bool.unifyBoolOr childTransformers term operand1 operand2
    --unifyBoolNot
  | Just (UnifyBoolNot (UnifyBoolNotArgs term operand value)) <- matchUnifyBoolNot first second
        = Builtin.Bool.unifyBoolNot childTransformers term operand value
    --unifyKEqualsEq
  | Just (UnifyKequalsEq (UnifyKequalsEqArgs eqTerm otherTerm)) <- matchUnifyKequalsEq first second
        = Builtin.KEqual.unifyKequalsEq childTransformers notSimplifier eqTerm otherTerm
    --unifyITE
  | Just (UnifyIfThenElse ifThenElse) <- matchITE first
        = Builtin.KEqual.unifyIfThenElse childTransformers ifThenElse second
  | Just (UnifyIfThenElse ifThenElse) <- matchITE second
        = Builtin.KEqual.unifyIfThenElse childTransformers ifThenElse first
    --unifyEquals endianness
  | Just (UnifyEqualsEndianness (UnifyEqualsEndiannessArgs end1 end2)) <- matchUnifyEqualsEndianness first second
        = Builtin.Endianness.unifyEquals first second end1 end2
   --unifyEquals signedness
  | Just (UnifyEqualsSignedness (UnifyEqualsSignednessArgs sign1 sign2)) <- matchUnifyEqualsSignedness first second
        = Builtin.Signedness.unifyEquals first second sign1 sign2
    --unifyEquals map
  | Just (UnifyEqualsMap1 (UnifyMapEqualsArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2)) <- matchUnifyEqualsMap tools first second
        = Builtin.Map.unifyEquals1 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2
  | Just (UnifyEqualsMap2 (UnifyMapEqualsVarArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var)) <- matchUnifyEqualsMap tools first second
        = Builtin.Map.unifyEquals2 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var
  | Just (UnifyEqualsMap3 (UnifyMapEqualsVarArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var)) <- matchUnifyEqualsMap tools first second
        = Builtin.Map.unifyEquals3 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var
  | Just UnifyMapBottom <- matchUnifyEqualsMap tools first second
        = lift $ Unify.explainAndReturnBottom
            "Duplicated elements in normalization." first second
    --unifyEquals set
  | Just (UnifyEqualsSet1 (UnifySetEqualsArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2)) <- matchUnifyEqualsSet tools first second
        = Builtin.Set.unifyEquals1 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2
  | Just (UnifyEqualsSet2 (UnifySetEqualsVarArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var)) <- matchUnifyEqualsSet tools first second
        = Builtin.Set.unifyEquals2 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var
  | Just (UnifyEqualsSet3 (UnifySetEqualsVarArgs preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var)) <- matchUnifyEqualsSet tools first second
        = Builtin.Set.unifyEquals3 tools first second childTransformers preElt1 preElt2 concreteElt1 concreteElt2 opaque1 opaque2 var
  | Just UnifySetBottom <- matchUnifyEqualsSet tools first second
        = lift $ Unify.explainAndReturnBottom
            "Duplicated elements in normalization." first second
    --unifyEqualsList
  | Just UnifyEqualsList1 <- matchUnifyEqualsList first' second'
        = Builtin.List.unify1 childTransformers first' second'
  | Just UnifyEqualsList2 <- matchUnifyEqualsList first' second'
        = Builtin.List.unify2 childTransformers first' second'
  | Just (UnifyEqualsList3 (UnifyEqualsList3Args symbol2 args1 args2)) <- matchUnifyEqualsList first' second'
        = Builtin.List.unify3 childTransformers first' second' symbol2 args1 args2
  | Just (UnifyEqualsList4 (UnifyEqualsList4Args builtin1 builtin2)) <- matchUnifyEqualsList first' second'
        = Builtin.List.unify4 childTransformers first' second' builtin1 builtin2
  | Just (UnifyEqualsList5 (UnifyEqualsList5Args builtin args)) <- matchUnifyEqualsList first' second'
        = Builtin.List.unify5 SimplificationType.Equals childTransformers first' second' args builtin
  | Just DomainValueAndConstructorErrors1 <- matchDomainValueAndConstructorErrors1 first second
        = domainValueAndConstructorErrors1 first second
  | Just DomainValueAndConstructorErrors2 <- matchDomainValueAndConstructorErrors2 first second
        = domainValueAndConstructorErrors2 first second
        --functionAnd
  | Just UnifyIsFunctionPatterns <- matchIsFunctionPatterns first second
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

-- | Unify two identical ('==') patterns.
equalAndEquals
    :: Monad unifier
    => TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
equalAndEquals first =
    return (Pattern.fromTermLike first)
    -- TODO: fix name

-- | Unify two patterns where the first is @\\bottom@.
bottomTermEquals
    :: MonadUnify unifier
    => SideCondition RewritingVariableName
    -> Sort
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
bottomTermEquals
    sideCondition
    sort
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
      where
        first = mkBottom sort

{- | Unify two patterns where the second is @\\bottom@.

See also: 'bottomTermEquals'

 -}
termBottomEquals
    :: MonadUnify unifier
    => SideCondition RewritingVariableName
    -> TermLike RewritingVariableName
    -> Sort
    -> MaybeT unifier (Pattern RewritingVariableName)
termBottomEquals sideCondition first sort =
    bottomTermEquals sideCondition sort first

variableFunctionAnd1
    :: InternalVariable variable
    => MonadUnify unifier
    => ElementVariable  variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
variableFunctionAnd1 v second
    = return $ Pattern.assign (inject v) second

variableFunctionAnd2
    :: InternalVariable variable
    => MonadUnify unifier
    => ElementVariable  variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
variableFunctionAnd2 v second
    = lift $ return (Pattern.withCondition second result)
  where result = Condition.fromSingleSubstitution
             (Substitution.assign (inject v) second)

{- | Unify a variable with a function pattern.

See also: 'isFunctionPattern'

 -}
variableFunctionEquals
    :: MonadUnify unifier
    => ElementVariable RewritingVariableName
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
variableFunctionEquals
    v
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
  | otherwise = empty
  where
      first = mkElemVar v

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
    -> Inj (TermLike RewritingVariableName)
    -> Inj (TermLike RewritingVariableName)
    -> MaybeT unifier (Pattern RewritingVariableName)
sortInjectionAndEquals termMerger inj1 inj2 = do
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
    first = mkInjWrap inj1
    second = mkInjWrap inj2

{- | Unify a constructor application pattern with a sort injection pattern.

Sort injections clash with constructors, so @constructorSortInjectionAndEquals@
returns @\\bottom@.

 -}
constructorSortInjectionAndEquals
    :: MonadUnify unifier
    => TermLike RewritingVariableName
    -> TermLike RewritingVariableName
    -> Symbol
    -> MaybeT unifier a
constructorSortInjectionAndEquals first second symbol2
  | Symbol.isConstructor symbol2 =
    lift $ noConfusionInjectionConstructor first second
  | otherwise = empty

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
    -> UnifyOverloadingResult unifier RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
overloadedConstructorSortInjectionAndEquals termMerger firstTerm secondTerm unifyResult
  = do
    eunifier <- lift . Error.runExceptT $ unifyResult
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
    => Sort
    -> TermLike RewritingVariableName
    -> Sort
    -> TermLike RewritingVariableName
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyDomainValue sort1 value1 sort2 value2 =
    assert (sort1 == sort2) $ lift worker
  where
    worker :: unifier (Pattern RewritingVariableName)
    worker
      | value1 == value2 =
        return $ Pattern.fromTermLike term1
      | otherwise = cannotUnifyDomainValues term1 term2
    term1 = mkDomainValue (DomainValue sort1 value1)
    term2 = mkDomainValue (DomainValue sort2 value2)

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
    => Text
    -> Text
    -> MaybeT unifier (Pattern RewritingVariableName)
unifyStringLiteral txt1 txt2 = lift worker
  where
    worker :: unifier (Pattern RewritingVariableName)
    worker
      | txt1 == txt1 =
        return $ Pattern.fromTermLike term1
      | otherwise = explainAndReturnBottom "distinct string literals" term1 term2
    term1 = mkStringLiteral txt1
    term2 = mkStringLiteral txt2

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

bytesDifferent
    :: MonadUnify unifier
    => InternalBytes
    -> InternalBytes
    -> MaybeT unifier (Pattern RewritingVariableName)
bytesDifferent bytesFirst bytesSecond
  | bytesFirst /= bytesSecond
    = return Pattern.bottom
bytesDifferent _ _ = empty
