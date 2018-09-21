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

import           Control.Monad.Counter
                 ( Counter )
import           Control.Monad.Except
                 ( ExceptT(..)  )
import           Data.Functor.Foldable
import           Data.Reflection
                 ( give )

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
                 ( Meta, MetaOrObject, Object )
import           Kore.AST.MLPatterns
                 ( getPatternResultSort )
import           Kore.AST.PureML
                 ( PureMLPattern )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeFalsePredicate )
import           Kore.Step.Simplification.AndTerms
                 ( termUnification )
import           Kore.Step.Simplification.Ceil
                 ( makeEvaluateTerm )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution(..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Error
                 ( UnificationError (..) )
import           Kore.Unification.UnifierImpl
                 ( UnificationProof (..) )
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
        )
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> PureMLPattern level variable
    -- ^left-hand-side of unification
    -> PureMLPattern level variable
    -> ExceptT
        -- TODO: Consider using a false predicate instead of a Left error
        UnificationError
        Counter
        ( PredicateSubstitution level variable
        , UnificationProof level variable
        )
unificationProcedure tools p1 p2
    | p1Sort /= p2Sort = return (bottom, EmptyUnificationProof)
    | otherwise = do
      let
          unifiedTerm = termUnification tools p1 p2
      (pat, _) <- ExceptT . sequence $ note UnsupportedPatterns unifiedTerm
      let
          (pred', _) = makeEvaluateTerm tools (ExpandedPattern.term pat)
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

      bottom = PredicateSubstitution makeFalsePredicate []

      note :: a -> Maybe b -> Either a b
      note a = maybe (Left a) Right
