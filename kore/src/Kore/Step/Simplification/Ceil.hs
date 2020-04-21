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

import Control.Error
    ( MaybeT
    , maybeT
    )
import Control.Monad.Reader
    ( ReaderT (..)
    )
import qualified Data.Foldable as Foldable
import qualified Data.Functor.Foldable as Recursive

import qualified Kore.Attribute.Symbol as Attribute.Symbol
    ( isTotal
    )
import qualified Kore.Builtin.AssocComm.CeilSimplifier as AssocComm
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (..)
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
import qualified Kore.Sort as Sort
import qualified Kore.Step.Function.Evaluator as Axiom
    ( evaluatePattern
    )
import qualified Kore.Step.Simplification.AndPredicates as And
import Kore.Step.Simplification.CeilSimplifier
import Kore.Step.Simplification.InjSimplifier
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
        makeEvaluateBuiltin sideCondition child
        & flip maybeT return (makeSimplifiedCeil sideCondition Nothing term)

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

ceilSimplifierTermLike
    ::  InternalVariable variable
    =>  MonadSimplify simplifier
    =>  CeilSimplifier
            (ReaderT (SideCondition variable) simplifier)
            (TermLike variable)
            (OrCondition variable)
ceilSimplifierTermLike =
    CeilSimplifier $ \Ceil { ceilChild = termLike } ->
    lift $ ReaderT $ \sideCondition ->
        makeEvaluateTerm sideCondition termLike

{-| Evaluates the ceil of a domain value.
-}
makeEvaluateBuiltin
    :: forall variable simplifier
    .  InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> Builtin (TermLike variable)
    -> MaybeT simplifier (OrCondition variable)
makeEvaluateBuiltin sideCondition (Domain.BuiltinMap internalAc) =
    runCeilSimplifierWith
        (AssocComm.newMapCeilSimplifier ceilSimplifierTermLike)
        sideCondition
        Ceil
            { ceilResultSort = Sort.predicateSort
            , ceilOperandSort = builtinAcSort
            , ceilChild = internalAc
            }
  where
    Domain.InternalAc { builtinAcSort } = internalAc
makeEvaluateBuiltin sideCondition (Domain.BuiltinSet internalAc) =
    runCeilSimplifierWith
        (AssocComm.newSetCeilSimplifier ceilSimplifierTermLike)
        sideCondition
        Ceil
            { ceilResultSort = Sort.predicateSort
            , ceilOperandSort = builtinAcSort
            , ceilChild = internalAc
            }
  where
    Domain.InternalAc { builtinAcSort } = internalAc
makeEvaluateBuiltin sideCondition (Domain.BuiltinList l) = do
    children <- mapM (makeEvaluateTerm sideCondition) (Foldable.toList l)
    let
        ceils :: [OrCondition variable]
        ceils = children
    And.simplifyEvaluatedMultiPredicate sideCondition (MultiAnd.make ceils)
makeEvaluateBuiltin _ (Domain.BuiltinBool _) = return OrCondition.top
makeEvaluateBuiltin _ (Domain.BuiltinInt _) = return OrCondition.top
makeEvaluateBuiltin _ (Domain.BuiltinString _) = return OrCondition.top

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
