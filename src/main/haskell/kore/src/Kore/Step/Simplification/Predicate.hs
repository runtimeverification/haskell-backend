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

import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( Predicate, unwrapPredicate )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (StepPatternSimplifier) )
import           Kore.Unparser

{-| Simplifies a predicate, producing another predicate and a substitution,
without trying to reapply the substitution on the predicate.

TODO(virgil): Make this fully simplify.
-}
simplifyPartial
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -> Predicate level variable
    -> Simplifier
        ( PredicateSubstitution level variable
        , SimplificationProof level
        )
simplifyPartial
    substitutionSimplifier
    (StepPatternSimplifier simplifier)
    predicate
  = do
    (patternOr, _proof) <-
        simplifier substitutionSimplifier (unwrapPredicate predicate)
    case OrOfExpandedPattern.extractPatterns patternOr of
        [] -> return
            ( Predicated.bottomPredicate
            , SimplificationProof
            )
        [ Predicated
                { term = Top_ _
                , predicate = simplifiedPredicate
                , substitution = simplifiedSubstitution
                }
            ] -> return
                ( Predicated
                    { term = ()
                    , predicate = simplifiedPredicate
                    , substitution = simplifiedSubstitution
                    }
                , SimplificationProof
                )
        [patt] ->
            (error . show . Pretty.vsep)
                [ "Expecting a top term!"
                , unparse patt
                ]
        _ -> error ("Expecting at most one result " ++ show patternOr)
