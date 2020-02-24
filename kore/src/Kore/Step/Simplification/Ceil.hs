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

import Prelude.Kore

import Control.Monad
    ( zipWithM
    )
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive
import qualified Data.List as List
import qualified Data.Map.Strict as Map

import qualified Kore.Attribute.Symbol as Attribute.Symbol
    ( isTotal
    )
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition
    ( OrCondition
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
    ( makeCeilPredicate_
    , makeTruePredicate_
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Function.Evaluator as Axiom
    ( evaluatePattern
    )
import qualified Kore.Step.Simplification.AndPredicates as And
import qualified Kore.Step.Simplification.Equals as Equals
import Kore.Step.Simplification.InjSimplifier
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.TopBottom
import Kore.Unparser
    ( unparseToString
    )

{-| Simplify a 'Ceil' of 'OrPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates
-}
simplify
    :: (InternalVariable variable, MonadSimplify simplifier)
    => SideCondition variable
    -> Ceil Sort (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify
    sideCondition
    Ceil { ceilChild = child }
  =
    simplifyEvaluated sideCondition child

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
    :: InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyEvaluated sideCondition child =
    MultiOr.flatten <$> traverse (makeEvaluate sideCondition) child

{-| Evaluates a ceil given its child as an Pattern, see 'simplify'
for details.
-}
makeEvaluate
    :: InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluate sideCondition child
  | Pattern.isTop    child = return OrPattern.top
  | Pattern.isBottom child = return OrPattern.bottom
  | otherwise              = makeEvaluateNonBoolCeil sideCondition child

makeEvaluateNonBoolCeil
    :: InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> Pattern variable
    -> simplifier (OrPattern variable)
makeEvaluateNonBoolCeil sideCondition patt@Conditional {term}
  | isTop term =
    return $ OrPattern.fromPattern
        patt {term = mkTop_} -- erase the term's sort.
  | otherwise = do
    termCeil <- makeEvaluateTerm sideCondition term
    result <-
        And.simplifyEvaluatedMultiPredicate
            sideCondition
            (MultiAnd.make
                [ MultiOr.make [Condition.eraseConditionalTerm patt]
                , termCeil
                ]
            )
    return (fmap Pattern.fromCondition result)

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.
{-| Evaluates the ceil of a TermLike, see 'simplify' for details.
-}
-- NOTE (hs-boot): Please update Ceil.hs-boot file when changing the
-- signature.
makeEvaluateTerm
    :: forall variable simplifier
    .  InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> TermLike variable
    -> simplifier (OrCondition variable)
makeEvaluateTerm
    sideCondition
    term@(Recursive.project -> _ :< projected)
  =
    makeEvaluateTermWorker
  where
    makeEvaluateTermWorker
      | isTop term            = return OrCondition.top
      | isBottom term         = return OrCondition.bottom
      | isDefinedPattern term = return OrCondition.top

      | ApplySymbolF app <- projected
      , let Application { applicationSymbolOrAlias = patternHead } = app
      , let headAttributes = symbolAttributes patternHead
      , Attribute.Symbol.isTotal headAttributes = do
            let Application { applicationChildren = children } = app
            simplifiedChildren <- mapM (makeEvaluateTerm sideCondition) children
            let ceils = simplifiedChildren
            And.simplifyEvaluatedMultiPredicate
                sideCondition
                (MultiAnd.make ceils)

      | BuiltinF child <- projected =
        fromMaybe
            (makeSimplifiedCeil sideCondition Nothing term)
            (makeEvaluateBuiltin sideCondition child)

      | InjF inj <- projected = do
        InjSimplifier { evaluateCeilInj } <- askInjSimplifier
        (makeEvaluateTerm sideCondition . ceilChild . evaluateCeilInj)
            Ceil
                { ceilResultSort = termLikeSort term -- sort is irrelevant
                , ceilOperandSort = termLikeSort term
                , ceilChild = inj
                }

      | otherwise = do
        evaluation <- Axiom.evaluatePattern
            sideCondition
            Conditional
                { term = ()
                , predicate = makeTruePredicate_
                , substitution = mempty
                }
            (mkCeil_ term)
            (\maybeCondition ->
                OrPattern.fromPatterns
                . map Pattern.fromCondition
                . OrCondition.toConditions
                <$> makeSimplifiedCeil sideCondition maybeCondition term
            )
        return (fmap toCondition evaluation)

    toCondition Conditional {term = Top_ _, predicate, substitution} =
        Conditional {term = (), predicate, substitution}
    toCondition patt =
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
    .  InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> Builtin (TermLike variable)
    -> Maybe (simplifier (OrCondition variable))
makeEvaluateBuiltin
    sideCondition
    (Domain.BuiltinMap internalAc)
  =
    makeEvaluateNormalizedAc
        mkOpaqueAc
        sideCondition
        (Domain.unwrapAc builtinAcChild)
  where
    Domain.InternalAc { builtinAcChild } = internalAc
    mkOpaqueAc normalizedAc =
        mkBuiltinMap internalAc
            { Domain.builtinAcChild = Domain.wrapAc normalizedAc }
makeEvaluateBuiltin sideCondition (Domain.BuiltinList l) = Just $ do
    children <- mapM (makeEvaluateTerm sideCondition) (Foldable.toList l)
    let
        ceils :: [OrCondition variable]
        ceils = children
    And.simplifyEvaluatedMultiPredicate sideCondition (MultiAnd.make ceils)
makeEvaluateBuiltin
    sideCondition
    (Domain.BuiltinSet internalAc)
  =
    makeEvaluateNormalizedAc
        mkOpaqueAc
        sideCondition
        (Domain.unwrapAc builtinAcChild)
  where
    Domain.InternalAc { builtinAcChild } = internalAc
    mkOpaqueAc normalizedAc =
        mkBuiltinSet internalAc
            { Domain.builtinAcChild = Domain.wrapAc normalizedAc }
makeEvaluateBuiltin _ (Domain.BuiltinBool _) = Just $ return OrCondition.top
makeEvaluateBuiltin _ (Domain.BuiltinInt _) = Just $ return OrCondition.top
makeEvaluateBuiltin _ (Domain.BuiltinString _) = Just $ return OrCondition.top

type MkOpaqueAc normalized variable =
    Domain.NormalizedAc normalized (TermLike Concrete) (TermLike variable)
    -> TermLike variable

makeEvaluateNormalizedAc
    :: forall normalized variable simplifier
    .   ( InternalVariable variable
        , MonadSimplify simplifier
        , Traversable (Domain.Value normalized)
        , Domain.AcWrapper normalized
        )
    =>  MkOpaqueAc normalized variable
    ->  SideCondition variable
    ->  Domain.NormalizedAc
            normalized
            (TermLike Concrete)
            (TermLike variable)
    ->  Maybe (simplifier (OrCondition variable))
makeEvaluateNormalizedAc mkOpaqueAc sideCondition normalizedAc =
    TermLike.assertConstructorLikeKeys concreteKeys . Just $ do
        -- concreteKeys are defined by assumption
        definedKeys <- traverse defineAbstractKey abstractKeys
        definedOpaque <- traverse defineOpaque opaque
        definedValues <- traverse defineValue allValues
        -- concreteKeys are distinct by assumption
        distinctConcreteKeys <-
            traverse (flip distinctKey concreteKeys) abstractKeys
        distinctAbstractKeys <-
            zipWithM distinctKey
                abstractKeys
                (tail $ List.tails abstractKeys)
        let conditions :: MultiAnd (OrCondition variable)
            conditions =
                mconcat
                    [ MultiAnd.make definedKeys
                    , MultiAnd.make definedOpaque
                    , mconcat definedValues
                    , mconcat distinctConcreteKeys
                    , mconcat distinctAbstractKeys
                    , definedConcreteOpaquePairs
                    , definedAbstractOpaquePairs
                    , definedOpaquePairs
                    ]

        And.simplifyEvaluatedMultiPredicate sideCondition conditions
  where
    Domain.NormalizedAc
        { elementsWithVariables = abstractElements
        , concreteElements
        , opaque
        }
      = normalizedAc

    defineAbstractKey :: TermLike variable -> simplifier (OrCondition variable)
    defineAbstractKey = makeEvaluateTerm sideCondition

    defineOpaque :: TermLike variable -> simplifier (OrCondition variable)
    defineOpaque = makeEvaluateTerm sideCondition

    abstractKeys, concreteKeys :: [TermLike variable]
    abstractValues, concreteValues, allValues
        :: [Domain.Value normalized (TermLike variable)]
    (abstractKeys, abstractValues) =
        unzip (Domain.unwrapElement <$> abstractElements)
    concreteKeys = TermLike.fromConcrete <$> Map.keys concreteElements
    concreteValues = Map.elems concreteElements
    allValues = concreteValues <> abstractValues

    defineValue
        :: Domain.Value normalized (TermLike variable)
        -> simplifier (MultiAnd (OrCondition variable))
    defineValue =
        Foldable.foldlM worker mempty
      where
        worker multiAnd termLike = do
            evaluated <- makeEvaluateTerm sideCondition termLike
            return (multiAnd <> MultiAnd.singleton evaluated)

    distinctKey
        :: TermLike variable
        -> [TermLike variable]
        -> simplifier (MultiAnd (OrCondition variable))
    distinctKey thisKey otherKeys = do
        MultiAnd.make <$> traverse (notEquals thisKey) otherKeys

    notEquals t1 t2 =
        Equals.makeEvaluateTermsToPredicate tMin tMax sideCondition
        >>= Not.simplifyEvaluatedPredicate
      where
        -- Stabilize the order of terms under Equals.
        (tMin, tMax) = minMax t1 t2

    definedConcreteOpaquePairs =
        foldMap defineConcreteOpaque $ Map.toList concreteElements
    definedAbstractOpaquePairs =
        foldMap defineAbstractOpaque abstractElements

    defineConcreteOpaque
        :: (TermLike Concrete, Domain.Value normalized (TermLike variable))
        -> MultiAnd (OrCondition variable)
    defineConcreteOpaque elt =
        foldMap (defineConcreteOpaquePair elt) opaque

    defineConcreteOpaquePair
        :: (TermLike Concrete, Domain.Value normalized (TermLike variable))
        -> TermLike variable
        -> MultiAnd (OrCondition variable)
    defineConcreteOpaquePair (key, value) opaque1 =
        Domain.NormalizedAc
            { elementsWithVariables = mempty
            , concreteElements = Map.singleton key value
            , opaque = [opaque1]
            }
        & mkOpaqueAc
        & makeSimplified
        & MultiAnd.singleton

    defineAbstractOpaque
        :: Domain.Element normalized (TermLike variable)
        -> MultiAnd (OrCondition variable)
    defineAbstractOpaque elt =
        foldMap (defineAbstractOpaquePair elt) opaque

    defineAbstractOpaquePair
        :: Domain.Element normalized (TermLike variable)
        -> TermLike variable
        -> MultiAnd (OrCondition variable)
    defineAbstractOpaquePair elt opaque1 =
        Domain.NormalizedAc
            { elementsWithVariables = [elt]
            , concreteElements = mempty
            , opaque = [opaque1]
            }
        & mkOpaqueAc
        & makeSimplified
        & MultiAnd.singleton

    definedOpaquePairs :: MultiAnd (OrCondition variable)
    definedOpaquePairs =
        mconcat $ zipWith defineOpaquePairs opaque (tail $ List.tails opaque)

    defineOpaquePairs
        :: TermLike variable
        -> [TermLike variable]
        -> MultiAnd (OrCondition variable)
    defineOpaquePairs this others =
        foldMap (defineOpaquePair this) others

    defineOpaquePair
        :: TermLike variable
        -> TermLike variable
        -> MultiAnd (OrCondition variable)
    defineOpaquePair opaque1 opaque2 =
        Domain.NormalizedAc
            { elementsWithVariables = mempty
            , concreteElements = mempty
            , opaque = [opaque1, opaque2]
            }
        & mkOpaqueAc
        & makeSimplified
        & MultiAnd.singleton

    makeSimplified =
        OrCondition.fromPredicate
        . Predicate.markSimplifiedMaybeConditional Nothing
        . makeCeilPredicate_

{-| This handles the case when we can't simplify a term's ceil.

It returns the ceil of that term.

When the term's ceil implies the ceils of its subterms, this also @and@s
the subterms' simplified ceils to the result. This is needed because the
SMT solver can't infer a subterm's ceil from a term's ceil, so we
have to provide that information.

As an example, if we call @makeSimplifiedCeil@ for @f(g(x))@, and we don't
know how to simplify @ceil(g(x))@, the return value will be
@and(ceil(f(g(x))), ceil(g(x)))@.

-}
makeSimplifiedCeil
    :: (InternalVariable variable, MonadSimplify simplifier)
    => SideCondition variable
    -> Maybe SideCondition.Representation
    -> TermLike variable
    -> simplifier (OrCondition variable)
makeSimplifiedCeil
    sideCondition
    maybeCurrentCondition
    termLike@(Recursive.project -> _ :< termLikeF)
  = do
    childCeils <- if needsChildCeils
        then mapM (makeEvaluateTerm sideCondition) (Foldable.toList termLikeF)
        else return []
    And.simplifyEvaluatedMultiPredicate
        sideCondition
        (MultiAnd.make (unsimplified : childCeils))
  where
    needsChildCeils = case termLikeF of
        ApplyAliasF _ -> False
        EvaluatedF  _ -> False
        EndiannessF _ -> True
        SignednessF _ -> True
        AndF _ -> True
        ApplySymbolF _ -> True
        InjF _ -> True
        CeilF _ -> unexpectedError
        EqualsF _ -> unexpectedError
        ExistsF _ -> False
        IffF _ -> False
        ImpliesF _ -> False
        InF _ -> False
        NotF _ -> False
        BottomF _ -> unexpectedError
        BuiltinF (Domain.BuiltinMap _) -> True
        BuiltinF (Domain.BuiltinList _) -> True
        BuiltinF (Domain.BuiltinSet _) -> True
        BuiltinF (Domain.BuiltinInt _) -> unexpectedError
        BuiltinF (Domain.BuiltinBool _) -> unexpectedError
        BuiltinF (Domain.BuiltinString _) -> unexpectedError
        DomainValueF _ -> True
        FloorF _ -> False
        ForallF _ -> False
        InhabitantF _ -> False
        MuF _ -> False
        NuF _ -> False
        NextF _ -> True
        OrF _ -> False
        RewritesF _ -> False
        TopF _ -> unexpectedError
        StringLiteralF _ -> unexpectedError
        InternalBytesF _ -> unexpectedError
        VariableF _ -> False

    unsimplified =
        OrCondition.fromPredicate
        . Predicate.markSimplifiedMaybeConditional maybeCurrentCondition
        . makeCeilPredicate_
        $ termLike

    unexpectedError =
        error ("Unexpected term type: " ++ unparseToString termLike)
