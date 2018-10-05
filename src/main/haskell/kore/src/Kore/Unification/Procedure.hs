{-|
Module      : Kore.Unification.Procedure
Description : Unification procedure.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Unification.Procedure
    ( unificationProcedure
    ) where

import Control.Error.Util
       ( note )
import Control.Monad.Counter
       ( MonadCounter )
import Control.Monad.Except
       ( ExceptT (..) )
import Data.Functor.Foldable
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
                 ( Meta, MetaOrObject, Object )
import           Kore.AST.MLPatterns
                 ( getPatternResultSort )
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( bottom )
import           Kore.Step.Simplification.AndTerms
                 ( termUnification )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( MonadPredicateSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Data
                 ( UnificationProof (..) )
import           Kore.Unification.Error
                 ( UnificationError (..) )
import           Kore.Variables.Fresh
                 ( FreshVariable )


-- |'unificationProcedure' atempts to simplify @t1 = t2@, assuming @t1@ and @t2@
-- are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedure
    ::  ( SortedVariable variable
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , Show (variable level)
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> MonadPredicateSimplifier level m
    -> PureMLPattern level variable
    -- ^left-hand-side of unification
    -> PureMLPattern level variable
    -> ExceptT
        -- TODO: Consider using a false predicate instead of a Left error
        UnificationError
        m
        ( PredicateSubstitution level variable
        , UnificationProof level variable
        )
unificationProcedure tools predicateSimplifier p1 p2
    | p1Sort /= p2Sort =
      return (PredicateSubstitution.bottom, EmptyUnificationProof)
    | otherwise = do
      let
          unifiedTerm = termUnification tools predicateSimplifier p1 p2
      -- TODO(Vladimir): Since unification is a central piece, we should test if
      -- the predicate is false and, if so, return PredicateSubstitution.bottom.
      (pat, _) <- ExceptT . sequence $ note UnsupportedPatterns unifiedTerm
      let
          (pred', _) = Ceil.makeEvaluateTerm tools (ExpandedPattern.term pat)
      return
          ( PredicateSubstitution
                (fst $ give sortTools $
                     makeAndPredicate (ExpandedPattern.predicate pat) pred')
                (ExpandedPattern.substitution pat)
          , EmptyUnificationProof
          )
  where
      sortTools = MetadataTools.sortTools tools
      resultSort = getPatternResultSort sortTools

      p1Sort = resultSort (project p1)
      p2Sort = resultSort (project p2)
