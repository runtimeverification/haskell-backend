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

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfPredicateSubstitution )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.AndTerms
                 ( termUnification )
import qualified Kore.Step.Simplification.Ceil as Ceil
                 ( makeEvaluateTerm )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Data
                 ( UnificationProof (..) )
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError (..) )
import           Kore.Unparser
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
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , MetaOrObject level
        , FreshVariable variable
        , MonadCounter m
        )
    => MetadataTools level StepperAttributes
    -- ^functions yielding metadata for pattern heads
    -> PredicateSubstitutionSimplifier level m
    -> StepPattern level variable
    -- ^left-hand-side of unification
    -> StepPattern level variable
    -> ExceptT
        (UnificationOrSubstitutionError level variable)
        m
        ( OrOfPredicateSubstitution level variable
        , UnificationProof level variable
        )
unificationProcedure tools substitutionSimplifier p1 p2
  | p1Sort /= p2Sort =
    return (OrOfExpandedPattern.make [], EmptyUnificationProof)
  | otherwise = do
    let
        getUnifiedTerm =
            termUnification
                tools
                substitutionSimplifier
                p1
                p2
    (pat@Predicated { term, predicate, substitution }, _) <- getUnifiedTerm
    let
        (pred', _) = Ceil.makeEvaluateTerm tools term
    if Predicated.isBottom pat
        then return
            (OrOfExpandedPattern.make [], EmptyUnificationProof)
        else return
            ( OrOfExpandedPattern.make
                [ Predicated
                    { term = ()
                    , predicate = makeAndPredicate predicate pred'
                    , substitution
                    }
                ]
            , EmptyUnificationProof
            )
  where
      p1Sort = getSort p1
      p2Sort = getSort p2
