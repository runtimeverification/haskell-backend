{-|
Module      : Kore.Step.Axiom.Matcher
Description : Matches free-form patterns which can be used when applying
              Equals rules.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Axiom.Matcher
    ( matchAsUnification
    , unificationWithAppMatchOnTop
    ) where

import           Control.Applicative
                 ( (<|>) )
import           Control.Error.Util
                 ( just, nothing )
import           Control.Monad.Except
import qualified Control.Monad.Trans as Monad.Trans
import           Control.Monad.Trans.Maybe
                 ( MaybeT (..) )
import qualified Data.Foldable as Foldable
import qualified Data.Map as Map
import qualified Data.Set as Set

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Predicate as Conditional
                 ( Conditional (..), Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import qualified Kore.Step.Merging.OrPattern as OrPattern
import           Kore.Step.RecursiveAttributes
                 ( isFunctionPattern )
import           Kore.Step.Simplification.AndTerms
                 ( SortInjectionMatch (SortInjectionMatch),
                 simplifySortInjections )
import qualified Kore.Step.Simplification.AndTerms as SortInjectionMatch
                 ( SortInjectionMatch (..) )
import qualified Kore.Step.Simplification.AndTerms as SortInjectionSimplification
                 ( SortInjectionSimplification (..) )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, TermLikeSimplifier )
import           Kore.Step.Simplification.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Simplification.Data as Simplifier
import           Kore.Step.Substitution
                 ( createPredicatesAndSubstitutionsMergerExcept,
                 mergePredicatesAndSubstitutionsExcept )
import           Kore.Unification.Error
                 ( unsupportedPatterns )
import           Kore.Unification.Procedure
                 ( unificationProcedure )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- Matches two patterns based on their form.

Assumes that the two patterns have no common variables (quantified or not).

Returns Right bottom or Left when it can't handle the patterns. The
returned substitution substitutes only variables from the first pattern.

The meaning of a Right value is that the substitution holds IF the predicate
holds.

TODO: This is different from unification's meaning, so we should either
convert all bottoms to Left, or we should do it selectively. Doing
it selectively is not trivial, e.g. a bottom inside a function should become
Left, but inside a constructor we may be able to keep it as bottom.
-}
matchAsUnification
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => TermLike variable
    -> TermLike variable
    -> unifier (Predicate variable)
matchAsUnification first second = do
    substitutionSimplifier <- Simplifier.askSimplifierPredicate
    simplifier <- Simplifier.askSimplifierTermLike
    axiomIdToSimplifier <- Simplifier.askSimplifierAxioms
    let matchResult =
            match
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                Map.empty
                first
                second
    result <- runMaybeT matchResult
    maybe
        (Monad.Unify.throwUnificationError
            (unsupportedPatterns "Unknown match case." first second)
        )
        return
        result
  where

unificationWithAppMatchOnTop
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => TermLike variable
    -> TermLike variable
    -> unifier (Predicate variable)
unificationWithAppMatchOnTop first second = do
    tools <- Simplifier.askMetadataTools
    substitutionSimplifier <- Simplifier.askSimplifierPredicate
    simplifier <- Simplifier.askSimplifierTermLike
    axiomIdToSimplifier <- Simplifier.askSimplifierAxioms
    case first of
        (App_ firstHead firstChildren) ->
            case second of
                (App_ secondHead secondChildren)
                  | firstHead == secondHead
                    -> unifyJoin
                            tools
                            substitutionSimplifier
                            simplifier
                            axiomIdToSimplifier
                            (zip firstChildren secondChildren)
                  | symbolOrAliasConstructor firstHead
                        == symbolOrAliasConstructor secondHead
                    -- The application heads have the same symbol or alias
                    -- constructor with different parameters,
                    -- but we do not handle unification of symbol parameters.
                        -> Monad.Unify.throwUnificationError
                            (unsupportedPatterns
                                "Unknown application head match case for "
                                first
                                second
                            )
                  | otherwise
                    -> error
                        (  "Unexpected unequal heads: "
                        ++ show firstHead ++ " and "
                        ++ show secondHead ++ "."
                        )
                _ -> error
                    (  "Expecting application patterns, but second = "
                    ++ show second ++ "."
                    )
        (Ceil_ firstOperandSort (SortVariableSort _) firstChild) ->
            case second of
                (Ceil_ secondOperandSort _resultSort secondChild)
                  | firstOperandSort == secondOperandSort ->
                    unificationWithAppMatchOnTop firstChild secondChild
                  | otherwise
                        -> error
                            (  "Unexpected unequal child sorts: "
                            ++ show firstOperandSort ++ " and "
                            ++ show secondOperandSort ++ "."
                            )
                _ -> error
                    (  "Expecting ceil patterns, but second = "
                    ++ show second ++ "."
                    )
        _ -> error
            (  "Expecting application or ceil with sort variable patterns, "
            ++ "but first = " ++ show first ++ "."
            )

match
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Map.Map variable variable
    -> TermLike variable
    -> TermLike variable
    -- TODO: Use Result here.
    -> MaybeT unifier (Predicate variable)
match
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    quantifiedVariables
    first
    second
  = do
    tools <- Simplifier.askMetadataTools
    (<|>)
        (matchEqualHeadPatterns
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            quantifiedVariables
            first
            second
        )
        (matchVariableFunction
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            quantifiedVariables
            first
            second
        )

matchEqualHeadPatterns
    ::  forall variable unifier
    .   ( SortedVariable variable
        , Unparse variable
        , Show variable
        , FreshVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Map.Map variable variable
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Predicate variable)
matchEqualHeadPatterns
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    quantifiedVariables
    first
    second
  =
    case first of
        (And_ _ firstFirst firstSecond) ->
            case second of
                (And_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (App_ firstHead firstChildren) ->
            case second of
                (App_ secondHead secondChildren) ->
                    if firstHead == secondHead
                    then
                        matchJoin
                            tools
                            substitutionSimplifier
                            simplifier
                            axiomIdToSimplifier
                            quantifiedVariables
                            (zip firstChildren secondChildren)
                    else case simplifySortInjections tools first second of
                        Nothing -> nothing
                        Just SortInjectionSimplification.NotInjection ->
                            nothing
                        Just SortInjectionSimplification.NotMatching ->
                            nothing
                        Just
                            (SortInjectionSimplification.Matching
                                SortInjectionMatch
                                    { firstChild, secondChild }
                            ) ->
                                matchJoin
                                    tools
                                    substitutionSimplifier
                                    simplifier
                                    axiomIdToSimplifier
                                    quantifiedVariables
                                    [(firstChild, secondChild)]
                _ -> nothing
        (Bottom_ _) -> topWhenEqualOrNothing first second
        (Ceil_ _ _ firstChild) ->
            case second of
                (Ceil_ _ _ secondChild) ->
                    match
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        firstChild
                        secondChild
                _ -> nothing
        (CharLiteral_ _) ->
            topWhenEqualOrNothing first second
        (Builtin_ _) ->
            topWhenEqualOrNothing first second
        (DV_ _ _) ->
            topWhenEqualOrNothing first second
        (Equals_ _ _ firstFirst firstSecond) ->
            case second of
                (Equals_ _ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Exists_ _ firstVariable firstChild) ->
            case second of
                (Exists_ _ secondVariable secondChild) ->
                    checkVariableEscape [firstVariable, secondVariable]
                    <$> match
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        (Map.insert
                            firstVariable secondVariable quantifiedVariables
                        )
                        firstChild
                        secondChild
                _ -> nothing
        (Floor_ _ _ firstChild) ->
            case second of
                (Floor_ _ _ secondChild) ->
                    match
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        firstChild
                        secondChild
                _ -> nothing
        (Forall_ _ firstVariable firstChild) ->
            case second of
                (Forall_ _ secondVariable secondChild) ->
                    (<$>)
                        (checkVariableEscape [firstVariable, secondVariable])
                        (match
                            substitutionSimplifier
                            simplifier
                            axiomIdToSimplifier
                            (Map.insert
                                firstVariable
                                secondVariable
                                quantifiedVariables
                            )
                            firstChild
                            secondChild
                        )
                _ -> nothing
        (Iff_ _ firstFirst firstSecond) ->
            case second of
                (Iff_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Implies_ _ firstFirst firstSecond) ->
            case second of
                (Implies_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (In_ _ _ firstFirst firstSecond) ->
            case second of
                (In_ _ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Next_ _ firstChild) ->
            case second of
                (Next_ _ secondChild) ->
                    match
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        firstChild
                        secondChild
                _ -> nothing
        (Not_ _ firstChild) ->
            case second of
                (Not_ _ secondChild) ->
                    match
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        firstChild
                        secondChild
                _ -> nothing
        (Or_ _ firstFirst firstSecond) ->
            case second of
                (Or_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Rewrites_ _ firstFirst firstSecond) ->
            case second of
                (Rewrites_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (StringLiteral_ _) -> topWhenEqualOrNothing first second
        (Top_ _) -> topWhenEqualOrNothing first second
        (Var_ firstVariable) ->
            case second of
                (Var_ secondVariable) ->
                    case Map.lookup firstVariable quantifiedVariables of
                        Nothing -> nothing
                        Just variable ->
                            if variable == secondVariable
                            then justTop
                            else nothing
                _ -> nothing
        _ -> nothing
  where
    topWhenEqualOrNothing first' second' =
        if first' == second'
            then justTop
            else nothing
    justTop :: MaybeT unifier (Predicate variable)
    justTop = just Predicate.top

matchJoin
    ::  forall variable unifier
    .   ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Map.Map variable variable
    -> [(TermLike variable, TermLike variable)]
    -> MaybeT unifier (Predicate variable)
matchJoin
    _tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    quantifiedVariables
    patterns
  = do
    matched <-
        traverse  -- also does a cross-product of the unifier branches
            (uncurry $
                match
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    quantifiedVariables
            )
            patterns
    lift $ mergePredicatesAndSubstitutionsExcept
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        (map Conditional.predicate matched)
        (map Conditional.substitution matched)

unifyJoin
    ::  forall variable unifier
    .   ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> [(TermLike variable, TermLike variable)]
    -> unifier (Predicate variable)
unifyJoin
    _tools _substitutionSimplifier _simplifier _axiomIdToSimplifier patterns
  = do
    predicates <- traverse (uncurry unificationProcedure) patterns
    return (Foldable.fold predicates)

-- Note that we can't match variables to stuff which can have more than one
-- value, because if we take the axiom
-- x = x and exists y . y=x
-- and we try to apply it to, say, 'a or b', where a and b are constructors
-- without arguments, then we would get
-- a or b
--   = (a or b) and (exists y . y = (a or b))
--   = (a or b) and bottom
--   = bottom
--
-- However, we can match variables to non-total stuff by using ceil to
-- force the match to bottom whenever we lose totality. This
-- assumes that, when applying the match to a pattern p, it will be split
-- into (p-replacing-lhs-by-rhs[subst] and predicate) or (p and not predicate)
matchVariableFunction
    ::  ( FreshVariable variable
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Map.Map variable variable
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Predicate variable)
matchVariableFunction
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    quantifiedVariables
    (Var_ var)
    second
  | not (var `Map.member` quantifiedVariables)
    && isFunctionPattern tools second
  = Monad.Trans.lift $ do
    ceilOr <- Monad.Unify.liftSimplifier $
        Ceil.makeEvaluateTerm
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            second
    result <-
        OrPattern.mergeWithPredicateAssumesEvaluated
            (createPredicatesAndSubstitutionsMergerExcept
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
            )
            Conditional
                { term = ()
                , predicate = makeTruePredicate
                , substitution = Substitution.wrap [(var, second)]
                }
            ceilOr
    Monad.Unify.scatter result
matchVariableFunction _ _ _ _ _ _ _ = nothing

checkVariableEscape
    ::  ( Show variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => [variable]
    -> Predicate variable
    -> Predicate variable
checkVariableEscape vars predSubst
  | any (`Set.member` freeVars) vars = error
        "quantified variables in substitution or predicate escaping context"
  | otherwise = predSubst
  where
    freeVars = Predicate.freeVariables predSubst
