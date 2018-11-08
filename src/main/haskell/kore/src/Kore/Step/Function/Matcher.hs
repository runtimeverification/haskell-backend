{-|
Module      : Kore.Step.Function.Matcher
Description : Matches free-form patterns which can be used when applying
              Equals rules.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Matcher
    ( matchAsUnification
    ) where

import           Control.Applicative
                 ( (<|>) )
import           Control.Error.Util
                 ( just, nothing )
import           Control.Monad.Counter
                 ( MonadCounter )
import           Control.Monad.Except
import           Control.Monad.Trans.Except
                 ( ExceptT (..) )
import           Control.Monad.Trans.Maybe
                 ( MaybeT (..) )
import qualified Data.List as List
import qualified Data.Map as Map
import           Data.Reflection
                 ( Given, give )
import qualified Data.Set as Set

import           Kore.AST.Common
                 ( PureMLPattern, SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
                 ( pattern And_, pattern App_, pattern Bottom_, pattern Ceil_,
                 pattern CharLiteral_, pattern DV_, pattern Equals_,
                 pattern Exists_, pattern Floor_, pattern Forall_,
                 pattern Iff_, pattern Implies_, pattern In_, pattern Next_,
                 pattern Not_, pattern Or_, pattern Rewrites_,
                 pattern StringLiteral_, pattern Top_, pattern Var_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools, SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.RecursiveAttributes
                 ( isFunctionPattern )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier )
import qualified Kore.Step.Simplification.Equals as Equals
                 ( makeEvaluateTermsToPredicateSubstitution )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutionsExcept )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Error
                 ( UnificationError (..), UnificationOrSubstitutionError (..) )
import           Kore.Unification.Unifier
                 ( UnificationProof (..) )
import           Kore.Variables.Free
                 ( freePureVariables )
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
    ::  ( Hashable variable
        , FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Ord (variable Object)
        , Ord (variable Meta)
        , Show (variable level)
        , Show (variable Object)
        , Show (variable Meta)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> ExceptT
        (UnificationOrSubstitutionError level variable)
        m
        ( PredicateSubstitution level variable
        , UnificationProof level variable
        )
matchAsUnification tools substitutionSimplifier first second = do
    result <- runMaybeT matchResult
    case result of
        Nothing -> throwError (UnificationError UnsupportedPatterns)
        Just r -> return (r, EmptyUnificationProof)
  where
    matchResult = match tools substitutionSimplifier Map.empty first second

match
    ::  ( Hashable variable
        , FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Ord (variable Object)
        , Ord (variable Meta)
        , Show (variable level)
        , Show (variable Object)
        , Show (variable Meta)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> Map.Map (variable level) (variable level)
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -- TODO: Use Result here.
    -> MaybeT
        (ExceptT
            (UnificationOrSubstitutionError level variable)
            m
        )
        (PredicateSubstitution level variable)
match tools substitutionSimplifier quantifiedVariables first second =
    matchEqualHeadPatterns
        tools substitutionSimplifier quantifiedVariables first second
    <|> matchVariableFunction tools quantifiedVariables first second
    <|> matchNonVarToPattern tools substitutionSimplifier first second

matchEqualHeadPatterns
    :: ( Show (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , Show (variable Meta)
       , Show (variable Object)
       , FreshVariable variable
       , Hashable variable
       , MonadCounter m
       )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> Map.Map (variable level) (variable level)
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT
        (ExceptT
            (UnificationOrSubstitutionError level variable)
            m
        )
        (PredicateSubstitution level variable)
matchEqualHeadPatterns
    tools substitutionSimplifier quantifiedVariables first second
  =
    case first of
        (And_ _ firstFirst firstSecond) ->
            case second of
                (And_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
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
                            quantifiedVariables
                            (zip firstChildren secondChildren)
                    else nothing
                _ -> nothing
        (Bottom_ _) -> topWhenEqualOrNothing first second
        (Ceil_ _ _ firstChild) ->
            case second of
                (Ceil_ _ _ secondChild) ->
                    match
                        tools
                        substitutionSimplifier
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
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> nothing
        (Exists_ _ firstVariable firstChild) ->
            case second of
                (Exists_ _ secondVariable secondChild) ->
                    give (MetadataTools.symbolOrAliasSorts tools)
                    $ checkVariableEscape [firstVariable, secondVariable]
                    <$> match
                        tools
                        substitutionSimplifier
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
                        quantifiedVariables
                        firstChild
                        secondChild
                _ -> nothing
        (Forall_ _ firstVariable firstChild) ->
            case second of
                (Forall_ _ secondVariable secondChild) ->
                    give (MetadataTools.symbolOrAliasSorts tools)
                    $ checkVariableEscape [firstVariable, secondVariable]
                    <$> match
                        tools
                        substitutionSimplifier
                        (Map.insert
                            firstVariable secondVariable quantifiedVariables
                        )
                        firstChild
                        secondChild
                _ -> nothing
        (Iff_ _ firstFirst firstSecond) ->
            case second of
                (Iff_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        substitutionSimplifier
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
                            then just Predicated.topPredicate
                            else nothing
                _ -> nothing
        _ -> nothing
  where
    topWhenEqualOrNothing first' second' =
        if first' == second'
            then just Predicated.topPredicate
            else nothing

matchJoin
    ::  ( Hashable variable
        , FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , Show (variable Object)
        , Show (variable Meta)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> Map.Map (variable level) (variable level)
    -> [(PureMLPattern level variable, PureMLPattern level variable)]
    -> MaybeT
        (ExceptT
            (UnificationOrSubstitutionError level variable)
            m
        )
        (PredicateSubstitution level variable)
matchJoin tools substitutionSimplifier quantifiedVariables patterns
  = do
    matched <-
        traverse
            (uncurry $ match tools substitutionSimplifier quantifiedVariables)
            patterns
    (merged, _proof) <- lift $ mergePredicatesAndSubstitutionsExcept
        tools
        substitutionSimplifier
        (map Predicated.predicate matched)
        (map Predicated.substitution matched)
    return merged

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
    :: ( Show (variable level)
       , SortedVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , MonadCounter m
       )
    => MetadataTools level StepperAttributes
    -> Map.Map (variable level) (variable level)
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT m (PredicateSubstitution level variable)
matchVariableFunction
    tools
    quantifiedVariables
    (Var_ var)
    second
  | not (var `Map.member` quantifiedVariables)
    && isFunctionPattern tools second
  = case Ceil.makeEvaluateTerm tools second of
        (predicate, _proof) ->
            just $
                Predicated
                    { term = ()
                    , predicate
                    , substitution = [(var, second)]
                    }
matchVariableFunction _ _ _ _ = nothing

matchNonVarToPattern
    :: ( Hashable variable
        , FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Ord (variable Object)
        , Ord (variable Meta)
        , Show (variable level)
        , Show (variable Object)
        , Show (variable Meta)
        , SortedVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level m
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> MaybeT
        (ExceptT
            (UnificationOrSubstitutionError level variable)
            m
        )
        (PredicateSubstitution level variable)
matchNonVarToPattern tools substitutionSimplifier first second
  -- TODO(virgil): For simplification axioms this would need to return bottom!
  = give (MetadataTools.symbolOrAliasSorts tools) $
    MaybeT $ lift $ do -- MonadCounter
        (Predicated {predicate, substitution}, _proof) <-
            Equals.makeEvaluateTermsToPredicateSubstitution
                tools substitutionSimplifier first second
        let
            -- We're only interested in substitutions involving first's
            -- variables here, and we're converting everything else to
            -- predicates.
            -- TODO: Make a function for this.
            leftVars = freePureVariables first
            (leftSubst, rightSubst) =
                List.partition ((`elem` leftVars) . fst) substitution
            finalPredicate = Predicated.toPredicate
                Predicated { term = (), predicate, substitution = rightSubst }
        (return . return)
            Predicated
                { term = ()
                , predicate = finalPredicate
                , substitution = leftSubst
                }

checkVariableEscape
    :: ( MetaOrObject level
        , Show (variable Object)
        , Show (variable Meta)
        , Ord (variable Object)
        , Ord (variable Meta)
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Eq (variable level)
        , Ord (variable level)
        , Show (variable level))
    => [variable level]
    -> PredicateSubstitution level variable
    -> PredicateSubstitution level variable
checkVariableEscape vars predSubst
  | any (`Set.member` freeVars) vars = error
        "quantified variables in substitution or predicate escaping context"
  | otherwise = predSubst
  where
    freeVars = Predicated.freeVariables predSubst
