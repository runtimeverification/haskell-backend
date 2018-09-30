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

import           Data.Either
                 ( isRight )
import qualified Data.Map as Map
import           Data.Maybe
                 ( catMaybes, listToMaybe )
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )

import           Control.Monad.Counter
                 ( Counter )
import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern And_, pattern App_, pattern Bottom_, pattern Ceil_,
                 pattern CharLiteral_, pattern DV_, pattern Equals_,
                 pattern Exists_, pattern Floor_, pattern Forall_,
                 pattern Iff_, pattern Implies_, pattern In_, pattern Next_,
                 pattern Not_, pattern Or_, pattern Rewrites_,
                 pattern StringLiteral_, pattern Top_, pattern Var_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate )
import           Kore.Step.ExpandedPattern
                 ( substitutionToPredicate )
import           Kore.Step.PatternAttributes
                 ( isFunctionPattern )
import           Kore.Step.PredicateSubstitution
                 ( PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( PredicateSubstitution (..), top )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import qualified Kore.Step.Simplification.Equals as Equals
                 ( makeEvaluateTermsToPredicateSubstitution )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Error
                 ( UnificationError (..) )
import           Kore.Unification.Unifier
                 ( UnificationProof (..) )
import           Kore.Variables.Free
                 ( pureFreeVariables )
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
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Either
        UnificationError
        (Counter
            ( PredicateSubstitution level variable
            , UnificationProof level variable
            )
        )
matchAsUnification tools first second =
    case match tools Map.empty first second of
        Nothing -> Left UnsupportedPatterns
        Just result -> return $ do  -- Counter monad
            predicateSubstitution <- result
            return (predicateSubstitution, EmptyUnificationProof)

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
        )
    => MetadataTools level StepperAttributes
    -> Map.Map (variable level) (variable level)
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (Counter (PredicateSubstitution level variable))
match tools quantifiedVariables first second =
    firstJust
        [ matchEqualHeadPatterns tools quantifiedVariables first second
        , matchVariableFunction tools quantifiedVariables first second
        , matchNonVarToPattern tools first second
        ]
  where
    firstJust :: [Maybe a] -> Maybe a
    firstJust = listToMaybe . catMaybes

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
       )
    => MetadataTools level StepperAttributes
    -> Map.Map (variable level) (variable level)
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (Counter (PredicateSubstitution level variable))
matchEqualHeadPatterns tools quantifiedVariables first second =
    case first of
        (And_ _ firstFirst firstSecond) ->
            case second of
                (And_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> Nothing
        (App_ firstHead firstChildren) ->
            case second of
                (App_ secondHead secondChildren) ->
                    if firstHead == secondHead
                    then matchJoin
                        tools
                        quantifiedVariables
                        (zip firstChildren secondChildren)
                    else Nothing
                _ -> Nothing
        (Bottom_ _) ->
            case second of
                (Bottom_ _) -> Just $ return PredicateSubstitution.top
                _ -> Nothing
        (Ceil_ _ _ firstChild) ->
            case second of
                (Ceil_ _ _ secondChild) ->
                    match tools quantifiedVariables firstChild secondChild
                _ -> Nothing
        (CharLiteral_ _) ->
            case second of
                (CharLiteral_ _) ->
                    if first == second
                    then Just $ return PredicateSubstitution.top
                    else Nothing
                _ -> Nothing
        (DV_ _ _) ->
            case second of
                (DV_ _ _) ->
                    if first == second
                    then Just $ return PredicateSubstitution.top
                    else Nothing
                _ -> Nothing
        (Equals_ _ _ firstFirst firstSecond) ->
            case second of
                (Equals_ _ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> Nothing
        (Exists_ _ firstVariable firstChild) ->
            case second of
                (Exists_ _ secondVariable secondChild) ->
                    match
                        tools
                        (Map.insert
                            firstVariable secondVariable quantifiedVariables
                        )
                        firstChild
                        secondChild
                _ -> Nothing
        (Floor_ _ _ firstChild) ->
            case second of
                (Floor_ _ _ secondChild) ->
                    match tools quantifiedVariables firstChild secondChild
                _ -> Nothing
        (Forall_ _ firstVariable firstChild) ->
            case second of
                (Forall_ _ secondVariable secondChild) ->
                    match
                        tools
                        (Map.insert
                            firstVariable secondVariable quantifiedVariables
                        )
                        firstChild
                        secondChild
                _ -> Nothing
        (Iff_ _ firstFirst firstSecond) ->
            case second of
                (Iff_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> Nothing
        (Implies_ _ firstFirst firstSecond) ->
            case second of
                (Implies_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> Nothing
        (In_ _ _ firstFirst firstSecond) ->
            case second of
                (In_ _ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> Nothing
        (Next_ _ firstChild) ->
            case second of
                (Next_ _ secondChild) ->
                    match tools quantifiedVariables firstChild secondChild
                _ -> Nothing
        (Not_ _ firstChild) ->
            case second of
                (Not_ _ secondChild) ->
                    match tools quantifiedVariables firstChild secondChild
                _ -> Nothing
        (Or_ _ firstFirst firstSecond) ->
            case second of
                (Or_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> Nothing
        (Rewrites_ _ firstFirst firstSecond) ->
            case second of
                (Rewrites_ _ secondFirst secondSecond) ->
                    matchJoin
                        tools
                        quantifiedVariables
                        [ (firstFirst, secondFirst)
                        , (firstSecond, secondSecond)
                        ]
                _ -> Nothing
        (StringLiteral_ _) ->
            case second of
                (StringLiteral_ _) ->
                    if first == second
                    then Just $ return PredicateSubstitution.top
                    else Nothing
                _ -> Nothing
        (Top_ _) ->
            case second of
                (Top_ _) -> Just $ return PredicateSubstitution.top
                _ -> Nothing
        (Var_ firstVariable) ->
            case second of
                (Var_ secondVariable) ->
                    case Map.lookup firstVariable quantifiedVariables of
                        Nothing -> Nothing
                        Just variable ->
                            if variable == secondVariable
                            then Just $ return PredicateSubstitution.top
                            else Nothing
                _ -> Nothing

matchJoin
    :: ( Hashable variable
       , FreshVariable variable
       , MetaOrObject level
       , Ord (variable level)
       , Ord (variable Meta)
       , Ord (variable Object)
       , Show (variable level)
       , Show (variable Object)
       , Show (variable Meta)
       , SortedVariable variable
       )
    => MetadataTools level StepperAttributes
    -> Map.Map (variable level) (variable level)
    -> [(PureMLPattern level variable, PureMLPattern level variable)]
    -> Maybe
        (Counter (PredicateSubstitution level variable))
matchJoin tools quantifiedVariables patterns = do -- Maybe monad
    matchedCounters <-
        traverse (uncurry $ match tools quantifiedVariables) patterns
    return $ do -- Counter monad
        matched <- sequenceA matchedCounters
        (merged, _proof) <- mergePredicatesAndSubstitutions
            tools
            (map PredicateSubstitution.predicate matched)
            (map PredicateSubstitution.substitution matched)
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
       )
    => MetadataTools level StepperAttributes
    -> Map.Map (variable level) (variable level)
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (Counter (PredicateSubstitution level variable))
matchVariableFunction
    tools
    quantifiedVariables
    (Var_ var)
    second
  | not (var `Map.member` quantifiedVariables)
    && isRight (isFunctionPattern tools second)
  =
    case Ceil.makeEvaluateTerm tools second of
        (predicate, _proof) ->
            Just $ return
                PredicateSubstitution
                    { predicate = predicate
                    , substitution = [(var, second)]
                    }
matchVariableFunction _ _ _ _ = Nothing

matchNonVarToPattern
    :: forall variable level .
        ( Hashable variable
        , FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Ord (variable Object)
        , Ord (variable Meta)
        , Show (variable level)
        , Show (variable Object)
        , Show (variable Meta)
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPattern level variable
    -> PureMLPattern level variable
    -> Maybe (Counter (PredicateSubstitution level variable))
matchNonVarToPattern tools first second
  | null (pureFreeVariables (Proxy :: Proxy level) first)
  = give (MetadataTools.symSorts tools) $
    return $ do -- Counter monad
        (PredicateSubstitution {predicate, substitution}, _proof) <-
            Equals.makeEvaluateTermsToPredicateSubstitution tools first second
        let
            -- We're only interested in substitutions involving first's
            -- variables
            -- here, and there are no free variables in the RHS, so we're
            -- coverting everything else to predicates.
            -- TODO: Make a function for this.
            (finalPredicate, _proof) =
                makeAndPredicate
                    predicate
                    (substitutionToPredicate substitution)
        return
            PredicateSubstitution
                { predicate = finalPredicate
                , substitution = []
                }
matchNonVarToPattern _ _ _ = Nothing
