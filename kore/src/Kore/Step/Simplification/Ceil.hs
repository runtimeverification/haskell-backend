{-|
Module      : Kore.Step.Simplification.Ceil
Description : Tools for Ceil pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Ceil
    ( simplify
    , makeEvaluate
    , makeEvaluateTerm
    , simplifyEvaluated
    , Ceil (..)
    ) where

import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )

import qualified Kore.Attribute.Symbol as Attribute.Symbol
                 ( isTotal )
import qualified Kore.Domain.Builtin as Domain
import           Kore.Internal.Conditional
                 ( Conditional (..) )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiAnd as MultiAnd
                 ( make )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import qualified Kore.Internal.OrPredicate as OrPredicate
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import           Kore.Logger
                 ( LogMessage, WithLog )
import           Kore.Predicate.Predicate
                 ( makeCeilPredicate, makeTruePredicate )
import qualified Kore.Step.Function.Evaluator as Axiom
                 ( evaluatePattern )
import qualified Kore.Step.Simplification.AndPredicates as And
import           Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Equals as Equals
import qualified Kore.Step.Simplification.Not as Not
import           Kore.TopBottom
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Simplify a 'Ceil' of 'OrPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates
-}
simplify
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => Ceil Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify Ceil { ceilChild = child } = simplifyEvaluated child

{-| 'simplifyEvaluated' evaluates a ceil given its child, see 'simplify'
for details.
-}
{- TODO (virgil): Preserve pattern sorts under simplification.

One way to preserve the required sort annotations is to make 'simplifyEvaluated'
take an argument of type

> CofreeF (Ceil Sort) (Attribute.Pattern variable) (OrPattern variable)

instead of an 'OrPattern' argument. The type of 'makeEvaluate' may
be changed analogously. The 'Attribute.Pattern' annotation will eventually cache
information besides the pattern sort, which will make it even more useful to
carry around.

-}
simplifyEvaluated
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated child =
    MultiOr.flatten <$> traverse makeEvaluate child

{-| Evaluates a ceil given its child as an Pattern, see 'simplify'
for details.
-}
makeEvaluate
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluate child
  | Pattern.isTop    child = return OrPattern.top
  | Pattern.isBottom child = return OrPattern.bottom
  | otherwise              = makeEvaluateNonBoolCeil child

makeEvaluateNonBoolCeil
    ::  ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluateNonBoolCeil patt@Conditional {term}
  | isTop term = return $ OrPattern.fromPattern patt
  | otherwise = do
    termCeil <- makeEvaluateTerm term
    result <-
        And.simplifyEvaluatedMultiPredicate
            (MultiAnd.make
                [ MultiOr.make [Predicate.eraseConditionalTerm patt]
                , termCeil
                ]
            )
    return (fmap Pattern.fromPredicate result)

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
{-| Evaluates the ceil of a TermLike, see 'simplify' for details.
-}
-- NOTE (hs-boot): Please update Ceil.hs-boot file when changing the
-- signature.
makeEvaluateTerm
    ::  forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => TermLike variable
    -> simplifier (OrPredicate variable)
makeEvaluateTerm term@(Recursive.project -> _ :< projected) =
    makeEvaluateTermWorker
  where
    makeEvaluateTermWorker
      | isTop term            = return OrPredicate.top
      | isBottom term         = return OrPredicate.bottom
      | isDefinedPattern term = return OrPredicate.top

      | ApplySymbolF app <- projected
      , let Application { applicationSymbolOrAlias = patternHead } = app
      , let headAttributes = symbolAttributes patternHead
      , Attribute.Symbol.isTotal headAttributes = do
            let Application { applicationChildren = children } = app
            simplifiedChildren <- mapM makeEvaluateTerm children
            let ceils = simplifiedChildren
            And.simplifyEvaluatedMultiPredicate (MultiAnd.make ceils)

      | BuiltinF child <- projected = makeEvaluateBuiltin child

      | otherwise = do
            substitutionSimplifier <- Simplifier.askSimplifierPredicate
            simplifier <- Simplifier.askSimplifierTermLike
            axiomIdToEvaluator <- Simplifier.askSimplifierAxioms
            evaluation <- Axiom.evaluatePattern
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                Conditional
                    { term = ()
                    , predicate = makeTruePredicate
                    , substitution = mempty
                    }
                (mkCeil_ term)
                (OrPattern.fromPattern Conditional
                    { term = mkTop_
                    , predicate = makeCeilPredicate term
                    , substitution = mempty
                    }
                )
            return (fmap toPredicate evaluation)

    toPredicate Conditional {term = Top_ _, predicate, substitution} =
        Conditional {term = (), predicate, substitution}
    toPredicate patt =
        error
            (  "Ceil simplification is expected to result ai a predicate, but"
            ++ " got (" ++ show patt ++ ")."
            ++ " The most likely cases are: evaluating predicate symbols, "
            ++ " and predicate symbols are currently unrecognized as such, "
            ++ "and programming errors."
            )

{-| Evaluates the ceil of a domain value.
-}
makeEvaluateBuiltin
    :: forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Unparse variable
        , Show variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Builtin (TermLike variable)
    -> simplifier (OrPredicate variable)
makeEvaluateBuiltin
    patt@(Domain.BuiltinMap Domain.InternalAc
        {builtinAcChild}
    )
  =
    fromMaybe
        (return unsimplified)
        (makeEvaluateNormalizedAc (Domain.unwrapAc builtinAcChild))
  where
    unsimplified =
        OrPredicate.fromPredicate
            (Predicate.fromPredicate
                (makeCeilPredicate (mkBuiltin patt))
            )
makeEvaluateBuiltin (Domain.BuiltinList l) = do
    children <- mapM makeEvaluateTerm (Foldable.toList l)
    let
        ceils :: [OrPredicate variable]
        ceils = children
    And.simplifyEvaluatedMultiPredicate (MultiAnd.make ceils)
makeEvaluateBuiltin
    patt@(Domain.BuiltinSet Domain.InternalAc
        {builtinAcChild}
    )
  =
    fromMaybe
        (return unsimplified)
        (makeEvaluateNormalizedAc (Domain.unwrapAc builtinAcChild))
  where
    unsimplified =
        OrPredicate.fromPredicate
            (Predicate.fromPredicate
                (makeCeilPredicate (mkBuiltin patt))
            )
makeEvaluateBuiltin (Domain.BuiltinBool _) = return OrPredicate.top
makeEvaluateBuiltin (Domain.BuiltinInt _) = return OrPredicate.top
makeEvaluateBuiltin (Domain.BuiltinString _) = return OrPredicate.top

makeEvaluateNormalizedAc
    :: forall normalized variable simplifier
    .   ( FreshVariable variable
        , MonadSimplify simplifier
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Traversable (Domain.Value normalized)
        , Unparse variable
        , Domain.AcWrapper normalized
        )
    =>  Domain.NormalizedAc
            normalized
            (TermLike Concrete)
            (TermLike variable)
    -> Maybe (simplifier (OrPredicate variable))
makeEvaluateNormalizedAc
    Domain.NormalizedAc
        { elementsWithVariables
        , concreteElements
        , opaque = []
        }
  = Just $ do
    variableKeyConditions <- mapM makeEvaluateTerm variableKeys
    variableValueConditions <- evaluateValues variableValues
    concreteValueConditions <- evaluateValues concreteValues

    elementsWithVariablesDistinct <-
        evaluateDistinct variableKeys concreteKeys
    let allConditions :: [OrPredicate variable]
        allConditions =
            concreteValueConditions
            ++ variableValueConditions
            ++ variableKeyConditions
            ++ elementsWithVariablesDistinct
    And.simplifyEvaluatedMultiPredicate (MultiAnd.make allConditions)
  where
    concreteElementsList
        ::  [   ( TermLike variable
                , Domain.Value normalized (TermLike variable)
                )
            ]
    concreteElementsList =
        map
            (\(a, b) -> (TermLike.fromConcrete a, b))
            (Map.toList concreteElements)
    (variableKeys, variableValues) =
        unzip (Domain.unwrapElement <$> elementsWithVariables)
    (concreteKeys, concreteValues) = unzip concreteElementsList

    evaluateDistinct
        :: [TermLike variable]
        -> [TermLike variable]
        -> simplifier [OrPredicate variable]
    evaluateDistinct [] _ = return []
    evaluateDistinct (variableTerm : variableTerms) concreteTerms = do
        equalities <-
            mapM
                (Equals.makeEvaluateTermsToPredicate variableTerm)
                -- TODO(virgil): consider eliminating these repeated
                -- concatenations.
                (variableTerms ++ concreteTerms)
        let negateEquality
                :: OrPredicate variable -> Predicate.Predicate variable
            negateEquality orPredicate =
                mergeAnd
                    (map
                        Not.makeEvaluatePredicate
                        (Foldable.toList orPredicate)
                    )
        let negations =
                map (OrPredicate.fromPredicate . negateEquality) equalities

        remainingConditions <-
            evaluateDistinct variableTerms concreteTerms
        return (negations ++ remainingConditions)

    evaluateValues
        :: [Domain.Value normalized (TermLike variable)]
        -> simplifier [OrPredicate variable]
    evaluateValues elements = do
        wrapped <- evaluateWrappers elements
        let unwrapped = map Foldable.toList wrapped
        return (concat unwrapped)
      where
        evaluateWrapper
            :: Domain.Value normalized (TermLike variable)
            -> simplifier (Domain.Value normalized (OrPredicate variable))
        evaluateWrapper = traverse makeEvaluateTerm

        evaluateWrappers
            :: [Domain.Value normalized (TermLike variable)]
            -> simplifier [Domain.Value normalized (OrPredicate variable)]
        evaluateWrappers = traverse evaluateWrapper

    mergeAnd :: [Predicate.Predicate variable] -> Predicate.Predicate variable
    mergeAnd [] = Predicate.top
    mergeAnd (predicate : predicates) =
        List.foldl' Conditional.andCondition predicate predicates
makeEvaluateNormalizedAc
    Domain.NormalizedAc
        { elementsWithVariables = []
        , concreteElements
        , opaque = [opaqueAc]
        }
  | Map.null concreteElements = Just $ makeEvaluateTerm opaqueAc
makeEvaluateNormalizedAc _ = Nothing
