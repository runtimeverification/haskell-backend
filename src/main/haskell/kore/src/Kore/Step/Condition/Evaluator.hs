{-|
Module      : Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Evaluator
    ( evaluate
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( SortedVariable, Variable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( SortTools, MetadataTools )
import           Kore.Predicate.Predicate
                 ( Predicate, makeAndPredicate, makeFalsePredicate, unwrapPredicate,
                 wrapPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..),
                 SimplificationProof (SimplificationProof), Simplifier )
import           Kore.SMT.SMT
{-| 'evaluate' attempts to evaluate a Kore predicate. -}
evaluate
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , Given (MetadataTools level SMTAttributes)
        )
    => PureMLPatternSimplifier level Variable
    -- ^ Evaluates functions in a pattern.
    -> Predicate level Variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> Simplifier
        (PredicateSubstitution level Variable, SimplificationProof level)
evaluate
    (PureMLPatternSimplifier simplifier)
    predicate''
  = do
    let predicate' = 
          if unsafeTryRefutePredicate predicate'' == Just False 
            then makeFalsePredicate
            else predicate'' 
    (patt, _proof) <- simplifier (unwrapPredicate predicate')
    let
       (subst, _proof) =
           asPredicateSubstitution (OrOfExpandedPattern.toExpandedPattern patt)
    return ( subst, SimplificationProof)

asPredicateSubstitution
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level)
        )
    => ExpandedPattern level variable
    -> (PredicateSubstitution level variable, SimplificationProof level)
asPredicateSubstitution
    ExpandedPattern {term, predicate, substitution}
  =
    let
        (andPatt, _proof) = makeAndPredicate predicate (wrapPredicate term)
    in
        ( PredicateSubstitution
            { predicate = andPatt
            , substitution = substitution
            }
        , SimplificationProof
        )
