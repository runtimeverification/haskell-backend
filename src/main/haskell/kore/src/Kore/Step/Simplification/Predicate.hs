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

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( Predicate, unwrapPredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as Predicated
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( extractPatterns )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (StepPatternSimplifier),
                 StepPatternSimplifier )
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

{-| Simplifies a predicate, producing another predicate and a substitution,
without trying to reapply the substitution on the predicate.

TODO(virgil): Make this fully simplify.
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
    case MultiOr.extractPatterns patternOr of
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
        [patt] -> error ("Expecting a top term! " ++ show patt)
        _ -> error ("Expecting at most one result " ++ show patternOr)
