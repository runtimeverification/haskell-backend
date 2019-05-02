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
import qualified Data.Map as Map
import qualified Data.Set as Set

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.TermLike
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Merging.OrPattern as OrPattern
import           Kore.Step.OrPredicate
                 ( OrPredicate )
import qualified Kore.Step.OrPredicate as OrPredicate
import           Kore.Step.Predicate as Conditional
                 ( Conditional (..), Predicate )
import qualified Kore.Step.Predicate as Predicate
import           Kore.Step.RecursiveAttributes
                 ( isFunctionPattern )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( extractPatterns, filterOr, fullCrossProduct, make )
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
import           Kore.Step.Substitution
                 ( createPredicatesAndSubstitutionsMergerExcept,
                 mergePredicatesAndSubstitutionsExcept )
import           Kore.Unification.Error
                 ( UnificationError (..) )
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
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> TermLike variable
    -> unifier
        ( OrPredicate variable

        )
matchAsUnification
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    first
    second
  = do
    result <- runMaybeT matchResult
    maybe (Monad.Unify.throwUnificationError UnsupportedPatterns) return result
  where
    matchResult =
        match
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            Map.empty
            first
            second

unificationWithAppMatchOnTop
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> TermLike variable
    -> unifier
        ( OrPredicate variable

        )
unificationWithAppMatchOnTop
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    first
    second
  = case first of
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
                  -> Monad.Unify.throwUnificationError UnsupportedPatterns
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
                | firstOperandSort == secondOperandSort
                    -> unificationWithAppMatchOnTop
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        firstChild
                        secondChild
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
        (  "Expecting application patterns, but second = "
        ++ show second ++ "."
        )

match
    ::  ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
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
    -- TODO: Use Result here.
    -> MaybeT unifier
        (OrPredicate variable)
match
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    quantifiedVariables
    first
    second
  =
    matchEqualHeadPatterns
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        quantifiedVariables
        first
        second
    <|> matchVariableFunction
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        quantifiedVariables
        first
        second

matchEqualHeadPatterns
    ::  forall variable unifier unifierM .
        ( Show variable
        , SortedVariable variable
        , Unparse variable
        , Show variable
        , FreshVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
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
    -> MaybeT unifier (OrPredicate variable)
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
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToSimplifier
                        quantifiedVariables
                        firstChild
                        secondChild
                _ -> nothing
        (CharLiteral_ _) ->
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
                    checkVariableEscapeOr [firstVariable, secondVariable]
                    <$> match
                        tools
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
                        tools
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
                        (checkVariableEscapeOr [firstVariable, secondVariable])
                        (match
                            tools
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
                        tools
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
                        tools
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
    justTop
        :: MaybeT unifier
            (OrPredicate variable)
    justTop = just
        (MultiOr.make [Predicate.top])

matchJoin
    :: forall variable unifier unifierM .
        ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Map.Map variable variable
    -> [(TermLike variable, TermLike variable)]
    -> MaybeT unifier
        (OrPredicate variable)
matchJoin
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    quantifiedVariables
    patterns
  = do
    matched <-
        traverse
            (uncurry $
                match
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    quantifiedVariables
            )
            patterns
    let
        crossProduct :: MultiOr [Predicate variable]
        crossProduct = MultiOr.fullCrossProduct matched
        merge :: [Predicate variable] -> unifier (Predicate variable)
        merge items =
            mergePredicatesAndSubstitutionsExcept
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                (map Conditional.predicate items)
                (map Conditional.substitution items)
    MultiOr.filterOr <$> traverse (lift . merge) crossProduct

unifyJoin
    :: forall variable unifier unifierM .
        ( FreshVariable variable
        , Show variable
        , Unparse variable
        , SortedVariable variable
        , MonadUnify unifierM
        , unifier ~ unifierM variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> [(TermLike variable, TermLike variable)]
    -> unifier
        ( OrPredicate variable

        )
unifyJoin
    tools substitutionSimplifier simplifier axiomIdToSimplifier patterns
  = do
    matched <-
        traverse
            (uncurry $
                unificationProcedure
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
            )
            patterns
    let
        crossProduct :: MultiOr [Predicate variable]
        crossProduct = MultiOr.fullCrossProduct matched
        merge
            :: [Predicate variable]
            -> unifier
                (Predicate variable)
        merge items =
            mergePredicatesAndSubstitutionsExcept
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                (map Conditional.predicate items)
                (map Conditional.substitution items)
    mergedItems <- mapM merge (MultiOr.extractPatterns crossProduct)
    return (OrPredicate.fromPredicates mergedItems)

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
        , MonadUnify unifierM
        , unifier ~ unifierM variable
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
    -> MaybeT unifier
        (OrPredicate variable)
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
                tools
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
    return result
matchVariableFunction _ _ _ _ _ _ _ = nothing

checkVariableEscapeOr
    ::  ( Show variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        )
    => [variable]
    -> OrPredicate variable
    -> OrPredicate variable
checkVariableEscapeOr vars = fmap (checkVariableEscape vars)

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
