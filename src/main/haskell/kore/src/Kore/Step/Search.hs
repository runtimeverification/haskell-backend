{-|
Module      : Kore.Step.Search
Description : Search functionality matching krun API
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
-}
module Kore.Step.Search
    ( SearchConfiguration (..)
    , SearchType (..)
    , search
    ) where

import Control.Error
       ( MaybeT (..) )
import Control.Error.Util
       ( hushT, nothing )
import Control.Monad.Trans.Class
       ( lift )
import Data.Maybe
       ( catMaybes )
import Data.Reflection
       ( give )
import Numeric.Natural
       ( Natural )

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
                 ( Meta (..), MetaOrObject, Object (..) )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeMultipleAndPredicate )
import           Kore.Step.BaseStep
                 ( StepProof )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, PureMLPatternSimplifier,
                 Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Strategy
                 ( Tree (..) )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Procedure
                 ( unificationProcedure )
import           Kore.Unification.Unifier
                 ( UnificationSubstitution )
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Says which configurations are to be considered for matching the pattern
-}
data SearchType
    = ONE
    -- ^reachable in one execution step
    | FINAL
    -- ^reachable configurations which cannot be rewritten anymore
    | STAR
    -- ^all reachable configurations
    | PLUS
    -- ^all configurations reachable in at least one step
 deriving (Eq, Show)

-- | Search setup configuration
data SearchConfiguration level variable =
    SearchConfiguration
    { start :: !(ExpandedPattern level variable)
    -- ^ pattern to start the execution with
    , bound :: !(Limit Natural)
    -- ^ maximum number of solutions
    , goal :: !(ExpandedPattern level variable)
    -- ^ pattern to match against the execution configurations.
    , searchType :: !SearchType
    }

{-| Implements search functionality to match the krun API.
Computes a list of solutions to the search problem.
A solution is a substitution unifying @pattern@ with an executing
configuration and satisfying the predicate of @pattern@.
-}
search
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Eq (variable level)
        , FreshVariable variable
        , Hashable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        , expanded ~ ExpandedPattern level variable
        , proof ~ StepProof level variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> PureMLPatternSimplifier level variable
    -> (expanded -> Simplifier (Tree (expanded, proof)))
    -> SearchConfiguration level variable
    -> Simplifier [UnificationSubstitution level variable]
search tools substitutionSimplifier simplifier strategy config = do
    executionTree <- strategy initialPattern
    let selectedConfigs = fst <$> pickStrategy executionTree
    matches <- catMaybes <$> traverse match selectedConfigs
    return (Limit.takeWithin boundLimit matches)
  where
    match patt =
        runMaybeT
            (matchWith
                tools
                substitutionSimplifier
                simplifier
                finalPattern
                patt
            )
    initialPattern = start config
    boundLimit = bound config
    finalPattern = goal config
    pickStrategy = case searchType config of
        ONE -> error "Not implemented!"
        PLUS -> error "Not implemented!"
        STAR -> error "Not implemented!"
        FINAL -> Strategy.pickFinal

matchWith
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Eq (variable level)
        , FreshVariable variable
        , Hashable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> PureMLPatternSimplifier level variable
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> MaybeT Simplifier (UnificationSubstitution level variable)
matchWith tools substitutionSimplifier simplifier e1 e2 = do
    (unifier, _proof) <- hushT (unificationProcedure tools t1 t2)
    let (predicate, _proof) = give (MetadataTools.symbolOrAliasSorts tools)
            $ makeMultipleAndPredicate
                [ PredicateSubstitution.predicate unifier
                , ExpandedPattern.predicate e1
                , ExpandedPattern.predicate e2
                ]
    (predSubst, _proof) <-
        give tools $ lift $ Predicate.evaluate substitutionSimplifier simplifier predicate
    let evaluatedPred = PredicateSubstitution.predicate predSubst
    case evaluatedPred of
        PredicateFalse -> nothing
        _ -> return (PredicateSubstitution.substitution unifier)
  where
    t1 = ExpandedPattern.term e1
    t2 = ExpandedPattern.term e2
