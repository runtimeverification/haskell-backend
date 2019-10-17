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
import qualified Data.Map as Map
import Data.Maybe
    ( fromMaybe
    )

import qualified Kore.Attribute.Symbol as Attribute.Symbol
    ( isTotal
    )
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( make
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.OrPredicate
    ( OrPredicate
    )
import qualified Kore.Internal.OrPredicate as OrPredicate
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import Kore.Logger
    ( LogMessage
    , WithLog
    )
import Kore.Predicate.Predicate
    ( makeCeilPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import qualified Kore.Step.Function.Evaluator as Axiom
    ( evaluatePattern
    )
import qualified Kore.Step.Simplification.AndPredicates as And
import qualified Kore.Step.Simplification.Equals as Equals
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.TopBottom

{-| Simplify a 'Ceil' of 'OrPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates
-}
simplify
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Predicate.Predicate variable
    -> Ceil Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify
    predicate
    Ceil { ceilChild = child }
  =
    simplifyEvaluated predicate child

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
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate.Predicate variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated predicate child =
    MultiOr.flatten <$> traverse (makeEvaluate predicate) child

{-| Evaluates a ceil given its child as an Pattern, see 'simplify'
for details.
-}
makeEvaluate
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate.Predicate variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluate predicate child
  | Pattern.isTop    child = return OrPattern.top
  | Pattern.isBottom child = return OrPattern.bottom
  | otherwise              = makeEvaluateNonBoolCeil predicate child

makeEvaluateNonBoolCeil
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate.Predicate variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluateNonBoolCeil predicate patt@Conditional {term}
  | isTop term = return $ OrPattern.fromPattern patt
  | otherwise = do
    termCeil <- makeEvaluateTerm predicate term
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
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate.Predicate variable
    -> TermLike variable
    -> simplifier (OrPredicate variable)
makeEvaluateTerm
    configurationPredicate
    term@(Recursive.project -> _ :< projected)
  =
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
            simplifiedChildren <- mapM
                                    (makeEvaluateTerm configurationPredicate)
                                    children
            let ceils = simplifiedChildren
            And.simplifyEvaluatedMultiPredicate (MultiAnd.make ceils)

      | BuiltinF child <- projected = makeEvaluateBuiltin
                                        configurationPredicate
                                        child

      | otherwise = do
        simplifier <- Simplifier.askSimplifierTermLike
        axiomIdToEvaluator <- Simplifier.askSimplifierAxioms
        evaluation <- Axiom.evaluatePattern
            simplifier
            axiomIdToEvaluator
            configurationPredicate
            Conditional
                { term = ()
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (mkCeil_ term)
            (OrPattern.fromPattern Conditional
                { term = mkTop_
                , predicate =
                    Syntax.Predicate.markSimplified
                    $ makeCeilPredicate term
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
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate.Predicate variable
    -> Builtin (TermLike variable)
    -> simplifier (OrPredicate variable)
makeEvaluateBuiltin
    predicate
    patt@(Domain.BuiltinMap Domain.InternalAc
        {builtinAcChild}
    )
  =
    fromMaybe
        (return unsimplified)
        (makeEvaluateNormalizedAc predicate (Domain.unwrapAc builtinAcChild))
  where
    unsimplified =
        OrPredicate.fromPredicate . Predicate.fromPredicate
        $ Syntax.Predicate.markSimplified . makeCeilPredicate $ mkBuiltin patt
makeEvaluateBuiltin predicate (Domain.BuiltinList l) = do
    children <- mapM (makeEvaluateTerm predicate) (Foldable.toList l)
    let
        ceils :: [OrPredicate variable]
        ceils = children
    And.simplifyEvaluatedMultiPredicate (MultiAnd.make ceils)
makeEvaluateBuiltin
    predicate
    patt@(Domain.BuiltinSet Domain.InternalAc
        {builtinAcChild}
    )
  =
    fromMaybe
        (return unsimplified)
        (makeEvaluateNormalizedAc predicate (Domain.unwrapAc builtinAcChild))
  where
    unsimplified =
        OrPredicate.fromPredicate
            (Predicate.fromPredicate
                (makeCeilPredicate (mkBuiltin patt))
            )
makeEvaluateBuiltin _ (Domain.BuiltinBool _) = return OrPredicate.top
makeEvaluateBuiltin _ (Domain.BuiltinInt _) = return OrPredicate.top
makeEvaluateBuiltin _ (Domain.BuiltinString _) = return OrPredicate.top

makeEvaluateNormalizedAc
    :: forall normalized variable simplifier
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , Traversable (Domain.Value normalized)
        , Domain.AcWrapper normalized
        )
    =>  Predicate.Predicate variable
    ->  Domain.NormalizedAc
            normalized
            (TermLike Concrete)
            (TermLike variable)
    -> Maybe (simplifier (OrPredicate variable))
makeEvaluateNormalizedAc
    configurationPredicate
    Domain.NormalizedAc
        { elementsWithVariables
        , concreteElements
        , opaque = []
        }
  = Just $ do
    variableKeyConditions <- mapM
                                (makeEvaluateTerm configurationPredicate)
                                variableKeys
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
                (flip
                    (Equals.makeEvaluateTermsToPredicate variableTerm)
                    configurationPredicate
                )
                -- TODO(virgil): consider eliminating these repeated
                -- concatenations.
                (variableTerms ++ concreteTerms)
        negations <- mapM Not.simplifyEvaluatedPredicate equalities

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
        evaluateWrapper = traverse (makeEvaluateTerm configurationPredicate)

        evaluateWrappers
            :: [Domain.Value normalized (TermLike variable)]
            -> simplifier [Domain.Value normalized (OrPredicate variable)]
        evaluateWrappers = traverse evaluateWrapper

makeEvaluateNormalizedAc
    configurationPredicate
    Domain.NormalizedAc
        { elementsWithVariables = []
        , concreteElements
        , opaque = [opaqueAc]
        }
  | Map.null concreteElements = Just $ makeEvaluateTerm
                                        configurationPredicate
                                        opaqueAc
makeEvaluateNormalizedAc _  _ = Nothing
