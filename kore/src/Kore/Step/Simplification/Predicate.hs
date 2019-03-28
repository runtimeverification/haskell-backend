{-|
Module      : Kore.Step.Simplification.Predicate
Description : Predicate simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Predicate
    ( simplifyPartial
    ) where

import qualified Control.Monad.Trans as Monad.Trans

import           Kore.AST.Pure
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Representation.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import           Kore.Step.Simplification.Data
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Simplify the 'Predicate' once; return but do not apply the substitution.

@simplifyPartial@ does not attempt to apply the resulting substitution and
re-simplify the result; see "Kore.Step.Simplification.PredicateSubstitution".

-}
simplifyPartial
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , Unparse (variable level)
        , SortedVariable variable
        )
    => PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -> Predicate level variable
    -> BranchT Simplifier (PredicateSubstitution level variable)
simplifyPartial
    substitutionSimplifier
    (StepPatternSimplifier simplifier)
    predicate
  = do
    (patternOr, _proof) <-
        Monad.Trans.lift
        $ simplifier substitutionSimplifier
        $ Predicate.unwrapPredicate predicate
    -- Despite using Monad.Trans.lift above, we do not need to explicitly check
    -- for \bottom because patternOr is an OrOfExpandedPattern.
    scatter (rewrapPredicate <$> patternOr)
  where
    rewrapPredicate predicated =
        predicated
            { term = ()
            , predicate =
                -- It is safe to re-wrap the simplified term as a predicate:
                -- simplifying a predicate must produce a predicate because
                -- simplification preserves sorts.
                Predicate.makeAndPredicate
                    (Predicate.wrapPredicate simplified)
                    predicate'
            }
      where
        Predicated { term = simplified, predicate = predicate' } = predicated
