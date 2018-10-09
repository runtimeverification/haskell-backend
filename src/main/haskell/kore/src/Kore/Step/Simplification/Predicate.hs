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

import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.Predicate.Predicate
                 ( Predicate, unwrapPredicate )
import           Kore.Step.ExpandedPattern
                 ( Predicated (Predicated) )
import qualified Kore.Step.ExpandedPattern as Predicated
                 ( Predicated (..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns )
import           Kore.Step.PredicateSubstitution
                 ( PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( PredicateSubstitution (..), bottom )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 PureMLPatternSimplifier (PureMLPatternSimplifier),
                 SimplificationProof (..), Simplifier )

{-| Simplifies a predicate, producing another predicate and a substitution,
without trying to reapply the substitution on the predicate.

TODO(virgil): Make this fully simplify.
-}
simplifyPartial
    ::  ( MetaOrObject level
        , Show (variable level)
        )
    => PredicateSubstitutionSimplifier level
    -> PureMLPatternSimplifier level variable
    -> Predicate level variable
    -> Simplifier
        ( PredicateSubstitution level variable
        , SimplificationProof level
        )
simplifyPartial
    substitutionSimplifier
    (PureMLPatternSimplifier simplifier)
    predicate
  = do
    (patternOr, _proof) <-
        simplifier substitutionSimplifier (unwrapPredicate predicate)
    case OrOfExpandedPattern.extractPatterns patternOr of
        [] -> return
            ( PredicateSubstitution.bottom
            , SimplificationProof
            )
        [Predicated
                { term = Top_ _
                , predicate = simplifiedPredicate
                , substitution = simplifiedSubstitution
                }
            ] -> return
                ( PredicateSubstitution
                    { predicate = simplifiedPredicate
                    , substitution = simplifiedSubstitution
                    }
                , SimplificationProof
                )
        [patt] -> error ("Expecting a top term! " ++ show patt)
        _ -> error ("Expecting at most one result " ++ show patternOr)
