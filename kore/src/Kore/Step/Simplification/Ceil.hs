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
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
    ( make
    , toPredicate
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeAndPredicate
    , makeCeilPredicate
    , makeEqualsPredicate
    , makeFalsePredicate
    , makeNotPredicate
    , makeTruePredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Function.Evaluator as Axiom
    ( evaluatePattern
    )
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
    => Condition variable
    -> Ceil Sort (OrPattern variable)
    -> simplifier (Pattern variable)
simplify
    condition
    Ceil { ceilChild = child }
  =
    simplifyEvaluated condition child

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
    :: SimplifierVariable variable
    => MonadSimplify simplifier
    => Condition variable
    -> OrPattern variable
    -> simplifier (Pattern variable)
simplifyEvaluated predicate child =
    OrPattern.toPattern <$> traverse (makeEvaluate predicate) child

{-| Evaluates a ceil given its child as an Pattern, see 'simplify'
for details.
-}
makeEvaluate
    :: SimplifierVariable variable
    => MonadSimplify simplifier
    => Condition variable
    -> Pattern variable
    -> simplifier (Pattern variable)
makeEvaluate predicate child
  | Pattern.isTop    child = return Pattern.top
  | Pattern.isBottom child = return Pattern.bottom
  | otherwise              = makeEvaluateNonBoolCeil predicate child

makeEvaluateNonBoolCeil
    :: forall simplifier variable
    .   ( MonadSimplify simplifier
        , SimplifierVariable variable
        )
    => Condition variable
    -> Pattern variable
    -> simplifier (Pattern variable)
makeEvaluateNonBoolCeil configurationCondition patt
  | isTop term =
    return $ Pattern.fromCondition condition
  | otherwise = do
    termCeil <- makeEvaluateTerm configurationCondition term
    let result :: Condition variable
        result = Conditional
            { term = ()
            , predicate = makeAndPredicate predicate termCeil
            , substitution
            }
    return (Pattern.fromCondition result)
  where
    (term, condition@Conditional {term = (), predicate, substitution}) =
        Pattern.splitTerm patt

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
{-| Evaluates the ceil of a TermLike, see 'simplify' for details.
-}
-- NOTE (hs-boot): Please update Ceil.hs-boot file when changing the
-- signature.
makeEvaluateTerm
    :: forall variable simplifier
    .  SimplifierVariable variable
    => MonadSimplify simplifier
    => Condition variable
    -> TermLike variable
    -> simplifier (Predicate variable)
makeEvaluateTerm
    configurationCondition
    term@(Recursive.project -> _ :< projected)
  =
    makeEvaluateTermWorker
  where
    makeEvaluateTermWorker
      | isTop term            = return makeTruePredicate
      | isBottom term         = return makeFalsePredicate
      | isDefinedPattern term = return makeTruePredicate

      | ApplySymbolF app <- projected
      , let Application { applicationSymbolOrAlias = patternHead } = app
      , let headAttributes = symbolAttributes patternHead
      , Attribute.Symbol.isTotal headAttributes = do
            let Application { applicationChildren = children } = app
            simplifiedChildren <- mapM
                (makeEvaluateTerm configurationCondition)
                children
            let ceils = simplifiedChildren
            return (MultiAnd.toPredicate (MultiAnd.make ceils))

      | BuiltinF child <- projected =
        makeEvaluateBuiltin configurationCondition child

      | otherwise = do
        evaluation <- Axiom.evaluatePattern
            configurationCondition
            Conditional
                { term = ()
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            (mkCeil_ term)
            (OrPattern.fromPattern Conditional
                { term = mkTop_
                , predicate =
                    Predicate.markSimplified
                    $ makeCeilPredicate term
                , substitution = mempty
                }
            )
        return
            ( OrCondition.toPredicate
            $ fmap (Condition.toPredicate . toCondition) evaluation
            )

    toCondition Conditional {term = Top_ _, predicate, substitution} =
        Conditional {term = (), predicate, substitution}
    toCondition patt =
        error
            (  "Ceil simplification is expected to result in a predicate, but"
            ++ " got (" ++ show patt ++ ")."
            ++ " The most likely cases are: evaluating predicate symbols, "
            ++ " and predicate symbols are currently unrecognized as such, "
            ++ "and programming errors."
            )

{-| Evaluates the ceil of a domain value.
-}
makeEvaluateBuiltin
    :: forall variable simplifier
    .  SimplifierVariable variable
    => MonadSimplify simplifier
    => Condition variable
    -> Builtin (TermLike variable)
    -> simplifier (Predicate variable)
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
        Predicate.markSimplified . makeCeilPredicate $ mkBuiltin patt
makeEvaluateBuiltin predicate (Domain.BuiltinList l) = do
    children <- mapM (makeEvaluateTerm predicate) (Foldable.toList l)
    let
        ceils :: [Predicate variable]
        ceils = children
    return (MultiAnd.toPredicate (MultiAnd.make ceils))
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
    unsimplified = Predicate.markSimplified (makeCeilPredicate (mkBuiltin patt))

makeEvaluateBuiltin _ (Domain.BuiltinBool _) = return makeTruePredicate
makeEvaluateBuiltin _ (Domain.BuiltinInt _) = return makeTruePredicate
makeEvaluateBuiltin _ (Domain.BuiltinString _) = return makeTruePredicate

makeEvaluateNormalizedAc
    :: forall normalized variable simplifier
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , Traversable (Domain.Value normalized)
        , Domain.AcWrapper normalized
        )
    =>  Condition variable
    ->  Domain.NormalizedAc
            normalized
            (TermLike Concrete)
            (TermLike variable)
    -> Maybe (simplifier (Predicate variable))
makeEvaluateNormalizedAc
    configurationCondition
    Domain.NormalizedAc
        { elementsWithVariables
        , concreteElements
        , opaque = []
        }
  = TermLike.assertNonSimplifiableKeys concreteKeys . Just $ do
    variableKeyConditions <- mapM
        (makeEvaluateTerm configurationCondition)
        variableKeys
    variableValueConditions <- evaluateValues variableValues
    concreteValueConditions <- evaluateValues concreteValues

    let elementsWithVariablesDistinct :: [Predicate variable]
        elementsWithVariablesDistinct =
            evaluateDistinct variableKeys concreteKeys
    let allConditions :: [Predicate variable]
        allConditions =
            concreteValueConditions
            ++ variableValueConditions
            ++ variableKeyConditions
            ++ elementsWithVariablesDistinct
    return $ MultiAnd.toPredicate (MultiAnd.make allConditions)
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
        -> [Predicate variable]
    evaluateDistinct [] _ = []
    evaluateDistinct (variableTerm : variableTerms) concreteTerms =
        let
            equalities :: [Predicate variable]
            equalities = map (makeEqualsPredicate variableTerm)
                (variableTerms ++ concreteTerms)
            negations :: [Predicate variable]
            negations = map makeNotPredicate equalities
            remainingConditions :: [Predicate variable]
            remainingConditions =
                evaluateDistinct variableTerms concreteTerms
        in (negations ++ remainingConditions)

    evaluateValues
        :: [Domain.Value normalized (TermLike variable)]
        -> simplifier [Predicate variable]
    evaluateValues elements = do
        wrapped <- evaluateWrappers elements
        let unwrapped = map Foldable.toList wrapped
        return (concat unwrapped)
      where
        evaluateWrapper
            :: Domain.Value normalized (TermLike variable)
            -> simplifier (Domain.Value normalized (Predicate variable))
        evaluateWrapper = traverse (makeEvaluateTerm configurationCondition)

        evaluateWrappers
            :: [Domain.Value normalized (TermLike variable)]
            -> simplifier [Domain.Value normalized (Predicate variable)]
        evaluateWrappers = traverse evaluateWrapper

makeEvaluateNormalizedAc
    configurationCondition
    Domain.NormalizedAc
        { elementsWithVariables = []
        , concreteElements
        , opaque = [opaqueAc]
        }
  | Map.null concreteElements =
    Just $ makeEvaluateTerm configurationCondition opaqueAc
makeEvaluateNormalizedAc _  _ = Nothing
