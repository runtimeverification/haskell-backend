{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.Ceil (
    simplify,
    makeEvaluate,
    makeEvaluateTerm,
    simplifyEvaluated,
    Ceil (..),
) where

import Control.Error (
    MaybeT,
    maybeT,
 )
import Control.Monad.Reader (
    MonadReader,
 )
import qualified Control.Monad.Reader as Reader
import qualified Data.Functor.Foldable as Recursive
import qualified Kore.Attribute.Symbol as Attribute.Symbol (
    isTotal,
 )
import Kore.Attribute.Synthetic (
    synthesize,
 )
import qualified Kore.Builtin.AssocComm.CeilSimplifier as AssocComm
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional (..),
 )
import Kore.Internal.InternalList
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    Representation,
 )
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Sort as Sort
import qualified Kore.Step.Function.Evaluator as Axiom (
    evaluatePattern,
 )
import qualified Kore.Step.Simplification.AndPredicates as And
import Kore.Step.Simplification.CeilSimplifier
import Kore.Step.Simplification.InjSimplifier
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.TopBottom
import Kore.Unparser (
    unparseToString,
 )
import Prelude.Kore

{- | Simplify a 'Ceil' of 'OrPattern'.

A ceil(or) is equal to or(ceil). We also take into account that
* ceil(top) = top
* ceil(bottom) = bottom
* ceil leaves predicates and substitutions unchanged
* ceil transforms terms into predicates
-}
simplify ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Ceil sort (OrPattern RewritingVariableName) ->
    simplifier (OrCondition RewritingVariableName)
simplify
    sideCondition
    Ceil{ceilChild = child} =
        simplifyEvaluated sideCondition child

{- | 'simplifyEvaluated' evaluates a ceil given its child, see 'simplify'
for details.
-}
simplifyEvaluated ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
simplifyEvaluated sideCondition child =
    OrPattern.traverseOr (makeEvaluate sideCondition) child

{- | Evaluates a ceil given its child as an Pattern, see 'simplify'
for details.
-}
makeEvaluate ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Pattern RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
makeEvaluate sideCondition child
    | Pattern.isTop child = return OrCondition.top
    | Pattern.isBottom child = return OrCondition.bottom
    | isTop term = return $ OrCondition.fromCondition condition
    | otherwise = do
        termCeil <- makeEvaluateTerm sideCondition term
        And.simplifyEvaluatedMultiPredicate
            sideCondition
            (MultiAnd.make [MultiOr.make [condition], termCeil])
  where
    (term, condition) = Pattern.splitTerm child

-- TODO: Ceil(function) should be an and of all the function's conditions, both
-- implicit and explicit.

-- | Evaluates the ceil of a TermLike, see 'simplify' for details.
makeEvaluateTerm ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
makeEvaluateTerm sideCondition ceilChild =
    runCeilSimplifierWith
        ceilSimplifier
        sideCondition
        Ceil
            { ceilResultSort = Sort.predicateSort
            , ceilOperandSort = termLikeSort ceilChild
            , ceilChild
            }
        & maybeT (makeSimplifiedCeil sideCondition Nothing ceilChild) return
  where
    ceilSimplifier =
        mconcat
            [ newPredicateCeilSimplifier
            , newDefinedCeilSimplifier sideCondition
            , -- We must apply user-defined \ceil rule before built-in rules
              -- because they may be more specific. In particular, Map and Set
              -- \ceil conditions are reduced to Bool expressions using in_keys.
              newAxiomCeilSimplifier
            , newApplicationCeilSimplifier
            , newBuiltinCeilSimplifier
            , newInjCeilSimplifier
            ]

newPredicateCeilSimplifier ::
    Monad simplifier =>
    CeilSimplifier
        simplifier
        (TermLike RewritingVariableName)
        (OrCondition RewritingVariableName)
newPredicateCeilSimplifier = CeilSimplifier $ \input ->
    case Predicate.makePredicate (ceilChild input) of
        Left _ -> empty
        Right predicate -> return (OrCondition.fromPredicate predicate)

newDefinedCeilSimplifier ::
    Monad simplifier =>
    SideCondition RewritingVariableName ->
    CeilSimplifier
        simplifier
        (TermLike RewritingVariableName)
        (OrCondition RewritingVariableName)
newDefinedCeilSimplifier sideCondition = CeilSimplifier $ \input ->
    if SideCondition.isDefined sideCondition (ceilChild input)
        then return OrCondition.top
        else empty

newApplicationCeilSimplifier ::
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    MonadSimplify simplifier =>
    InternalVariable RewritingVariableName =>
    CeilSimplifier
        simplifier
        (TermLike RewritingVariableName)
        (OrCondition RewritingVariableName)
newApplicationCeilSimplifier = CeilSimplifier $ \input ->
    case ceilChild input of
        App_ patternHead children
            | let headAttributes = symbolAttributes patternHead
              , Attribute.Symbol.isTotal headAttributes -> do
                sideCondition <- Reader.ask
                let mkChildCeil =
                        makeEvaluateTermCeil
                            sideCondition
                simplifiedChildren <- mapM mkChildCeil children
                let ceils = simplifiedChildren
                And.simplifyEvaluatedMultiPredicate
                    sideCondition
                    (MultiAnd.make ceils)
        _ -> empty

newInjCeilSimplifier ::
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    MonadSimplify simplifier =>
    CeilSimplifier
        simplifier
        (TermLike RewritingVariableName)
        (OrCondition RewritingVariableName)
newInjCeilSimplifier = CeilSimplifier $ \input ->
    case ceilChild input of
        Inj_ inj -> do
            InjSimplifier{evaluateCeilInj} <- askInjSimplifier
            sideCondition <- Reader.ask
            input{ceilChild = inj}
                & evaluateCeilInj
                & ceilChild
                & makeEvaluateTermCeil sideCondition
        _ -> empty

newBuiltinCeilSimplifier ::
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    MonadSimplify simplifier =>
    CeilSimplifier
        simplifier
        (TermLike RewritingVariableName)
        (OrCondition RewritingVariableName)
newBuiltinCeilSimplifier = CeilSimplifier $ \input ->
    case ceilChild input of
        InternalList_ internal -> do
            sideCondition <- Reader.ask
            makeEvaluateInternalList sideCondition internal
        InternalMap_ internalMap -> do
            sideCondition <- Reader.ask
            makeEvaluateInternalMap sideCondition internalMap
        InternalSet_ internalSet -> do
            sideCondition <- Reader.ask
            makeEvaluateInternalSet sideCondition internalSet
        _ -> empty

newAxiomCeilSimplifier ::
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    MonadSimplify simplifier =>
    CeilSimplifier
        simplifier
        (TermLike RewritingVariableName)
        (OrCondition RewritingVariableName)
newAxiomCeilSimplifier = CeilSimplifier $ \input -> do
    sideCondition <- Reader.ask
    evaluation <-
        Axiom.evaluatePattern
            sideCondition
            Condition.top
            (synthesize $ CeilF input)
            (const empty)
    return (OrPattern.map toCondition evaluation)
  where
    toCondition Conditional{term = Top_ _, predicate, substitution} =
        Conditional{term = (), predicate, substitution}
    toCondition patt =
        error
            ( "Ceil simplification is expected to result ai a predicate, but"
                ++ " got ("
                ++ show patt
                ++ ")."
                ++ " The most likely cases are: evaluating predicate symbols, "
                ++ " and predicate symbols are currently unrecognized as such, "
                ++ "and programming errors."
            )

makeEvaluateInternalMap ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    InternalMap Key (TermLike RewritingVariableName) ->
    MaybeT simplifier (OrCondition RewritingVariableName)
makeEvaluateInternalMap sideCondition internalMap =
    runCeilSimplifierWith
        AssocComm.newMapCeilSimplifier
        sideCondition
        Ceil
            { ceilResultSort = Sort.predicateSort
            , ceilOperandSort = builtinAcSort
            , ceilChild = internalMap
            }
  where
    InternalAc{builtinAcSort} = internalMap

-- | Evaluates the ceil of a domain value.
makeEvaluateInternalSet ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    InternalSet Key (TermLike RewritingVariableName) ->
    MaybeT simplifier (OrCondition RewritingVariableName)
makeEvaluateInternalSet sideCondition internalSet =
    runCeilSimplifierWith
        AssocComm.newSetCeilSimplifier
        sideCondition
        Ceil
            { ceilResultSort = Sort.predicateSort
            , ceilOperandSort = builtinAcSort
            , ceilChild = internalSet
            }
  where
    InternalAc{builtinAcSort} = internalSet

makeEvaluateInternalList ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    InternalList (TermLike RewritingVariableName) ->
    simplifier (OrCondition RewritingVariableName)
makeEvaluateInternalList sideCondition internal = do
    children <- mapM (makeEvaluateTerm sideCondition) (toList internal)
    let ceils :: [OrCondition RewritingVariableName]
        ceils = children
    And.simplifyEvaluatedMultiPredicate sideCondition (MultiAnd.make ceils)

{- | This handles the case when we can't simplify a term's ceil.

It returns the ceil of that term.

When the term's ceil implies the ceils of its subterms, this also @and@s
the subterms' simplified ceils to the result. This is needed because the
SMT solver can't infer a subterm's ceil from a term's ceil, so we
have to provide that information.

As an example, if we call @makeSimplifiedCeil@ for @f(g(x))@, and we don't
know how to simplify @ceil(g(x))@, the return value will be
@and(ceil(f(g(x))), ceil(g(x)))@.
-}
makeSimplifiedCeil ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Maybe SideCondition.Representation ->
    TermLike RewritingVariableName ->
    simplifier (OrCondition RewritingVariableName)
makeSimplifiedCeil
    sideCondition
    maybeCurrentCondition
    termLike@(Recursive.project -> _ :< termLikeF) =
        do
            childCeils <-
                if needsChildCeils
                    then mapM (makeEvaluateTerm sideCondition) (toList termLikeF)
                    else return []
            And.simplifyEvaluatedMultiPredicate
                sideCondition
                (MultiAnd.make (unsimplified : childCeils))
      where
        needsChildCeils = case termLikeF of
            ApplyAliasF _ -> False
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
            InternalBoolF _ -> unexpectedError
            InternalBytesF _ -> unexpectedError
            InternalIntF _ -> unexpectedError
            InternalListF _ -> True
            InternalMapF _ -> True
            InternalSetF _ -> True
            InternalStringF _ -> unexpectedError
            VariableF _ -> False

        unsimplified =
            OrCondition.fromPredicate
                . Predicate.markSimplifiedMaybeConditional maybeCurrentCondition
                . makeCeilPredicate
                $ termLike

        ~unexpectedError =
            error ("Unexpected term type: " ++ unparseToString termLike)
