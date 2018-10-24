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

import Control.Monad.Counter
       ( MonadCounter )
import Control.Monad.Except
       ( ExceptT (..) )
import Data.Functor.Foldable
import Data.Reflection
       ( give )

import           Kore.AST.Common
                 ( PureMLPattern, SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.MLPatterns
                 ( getPatternResultSort )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( Predicated (..), isBottom )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( bottom )
import           Kore.Step.Simplification.AndTerms
                 ( termUnification )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 liftPredicateSubstitutionSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Data
                 ( UnificationProof (..) )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError (..) )
import           Kore.Variables.Fresh
                 ( FreshVariable )


-- |'unificationProcedure' atempts to simplify @t1 = t2@, assuming @t1@ and @t2@
-- are terms (functional patterns) to a substitution.
-- If successful, it also produces a proof of how the substitution was obtained.
-- If failing, it gives a 'UnificationError' reason for the failure.
unificationProcedure
    ::  ( SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , MetaOrObject level
        , Hashable variable
        , FreshVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> PredicateSubstitutionSimplifier level m
    -> PureMLPattern level variable
    -- ^left-hand-side of unification
    -> PureMLPattern level variable
    -> ExceptT
        -- TODO: Consider using a false predicate instead of a Left error
        (UnificationOrSubstitutionError level variable)
        m
        ( PredicateSubstitution level variable
        , UnificationProof level variable
        )
unificationProcedure tools substitutionSimplifier p1 p2
  | p1Sort /= p2Sort =
    return (PredicateSubstitution.bottom, EmptyUnificationProof)
  | otherwise = do
    let
        getUnifiedTerm =
            termUnification
                tools
                (liftPredicateSubstitutionSimplifier substitutionSimplifier)
                p1
                p2
    (pat, _) <- getUnifiedTerm
    let
        (pred', _) = Ceil.makeEvaluateTerm tools (ExpandedPattern.term pat)
    if ExpandedPattern.isBottom pat
        then return
            ( PredicateSubstitution.bottom
            , EmptyUnificationProof
            )
        else return
            ( PredicateSubstitution
                (fst $ give symbolOrAliasSorts $
                    makeAndPredicate (ExpandedPattern.predicate pat) pred')
                (ExpandedPattern.substitution pat)
            , EmptyUnificationProof
            )
  where
      symbolOrAliasSorts = MetadataTools.symbolOrAliasSorts tools
      resultSort = getPatternResultSort symbolOrAliasSorts

      p1Sort = resultSort (project p1)
      p2Sort = resultSort (project p2)
