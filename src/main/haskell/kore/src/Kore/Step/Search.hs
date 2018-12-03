{-|
Module      : Kore.Step.Search
Description : Search functionality matching krun API
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
-}
module Kore.Step.Search
    ( Config (..)
    , SearchType (..)
    , searchGraph
    , matchWith
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
                 ( MetaOrObject, OrdMetaOrObject, ShowMetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Procedure
                 ( unificationProcedure )
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Which configurations are considered for matching?

See also: 'searchGraph'

 -}
data SearchType
    = ONE
    -- ^ Reachable in exactly one execution step
    | FINAL
    -- ^ Reachable configurations which cannot be rewritten anymore
    | STAR
    -- ^ All reachable configurations
    | PLUS
    -- ^ All configurations reachable in at least one step
 deriving (Eq, Show)

-- | Search options
data Config =
    Config
    { bound :: !(Limit Natural)
    -- ^ maximum number of solutions
    , searchType :: !SearchType
    }

{- | Construct a list of solutions to the execution search problem.

The execution tree can be generated with 'Kore.Step.Strategy.runStrategy' or any
of the related functions in "Kore.Step.Step".

The matching criterion returns a substitution which takes its argument to the
search goal (see 'matchWith'). The 'searchType' is used to restrict which states
may be considered for matching.

@searchGraph@ returns a list of substitutions which take the initial
configuration to the goal defined by the matching criterion. The number of
solutions returned is limited by 'bound'.

See also: 'Kore.Step.Strategy.runStrategy', 'matchWith'

-}
searchGraph
    :: Config  -- ^ Search options
    -> (config -> MaybeT Simplifier substitution)
        -- ^ Matching criterion
    -> Strategy.ExecutionGraph config
        -- ^ Execution tree
    -> Simplifier [substitution]
searchGraph Config { searchType, bound } match executionGraph = do
    let selectedConfigs = pick executionGraph
    matches <- catMaybes <$> traverse (runMaybeT . match) selectedConfigs
    return (Limit.takeWithin bound matches)
  where
    pick =
        case searchType of
            ONE -> Strategy.pickOne
            PLUS -> Strategy.pickPlus
            STAR -> Strategy.pickStar
            FINAL -> Strategy.pickFinal

matchWith
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Eq (variable level)
        , FreshVariable variable
        , Hashable variable
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> MaybeT Simplifier (PredicateSubstitution level variable)
matchWith tools substitutionSimplifier simplifier e1 e2 = do
    (unifier, _proof) <-
        hushT $ unificationProcedure tools substitutionSimplifier t1 t2
    (predSubst, _proof) <-
            lift
            $ mergePredicatesAndSubstitutions
                tools
                substitutionSimplifier
                [ Predicated.predicate unifier
                , Predicated.predicate e1
                , Predicated.predicate e2
                ]
                [ Predicated.substitution unifier ]
    (predSubst', _proof) <-
        give tools
        $ lift
        $ Predicate.evaluate substitutionSimplifier simplifier
        $ Predicated.predicate predSubst
    let evaluatedPred = Predicated.predicate predSubst'
    case evaluatedPred of
        PredicateFalse -> nothing
        _ ->
            lift
            $ fst <$> mergePredicatesAndSubstitutions
                tools
                substitutionSimplifier
                [ Predicated.predicate predSubst' ]
                [ Predicated.substitution predSubst'
                , Predicated.substitution predSubst
                ]
  where
    t1 = Predicated.term e1
    t2 = Predicated.term e2
