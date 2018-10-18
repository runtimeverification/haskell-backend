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
    , search
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
                 ( Meta (..), MetaOrObject, Object (..) )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeMultipleAndPredicate )
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

{-| Which configurations are considered for matching?

See also: 'search'

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

The execution strategy generates a tree of reachable states (see
'Kore.Step.Strategy.runStrategy'). The matching criterion returns a substitution
which takes its argument to the search goal (see 'matchWith'). The 'searchType'
is used to restrict which states may be considered for matching.

@search@ returns a list of substitutions which take the initial configuration to
the goal defined by the matching criterion. The number of solutions returned is
limited by 'bound'.

See also: 'Kore.Step.Strategy.runStrategy', 'matchWith'

-}
search
    :: Config  -- ^ Search options
    -> (config -> Simplifier (Tree (config, proof)))
        -- ^ Execution strategy
    -> (config -> MaybeT Simplifier substitution)
        -- ^ Matching criterion
    -> config  -- ^ Initial configuration
    -> Simplifier [substitution]
search Config { searchType, bound } strategy match initialPattern = do
    executionTree <- strategy initialPattern
    let selectedConfigs = fst <$> pick executionTree
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
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable level)
        , Show (variable Meta)
        , Show (variable Object)
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> PureMLPatternSimplifier level variable
    -> ExpandedPattern level variable
    -> ExpandedPattern level variable
    -> MaybeT Simplifier (UnificationSubstitution level variable)
matchWith tools substitutionSimplifier simplifier e1 e2 = do
    (unifier, _proof) <- hushT (unificationProcedure tools substitutionSimplifier t1 t2)
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
