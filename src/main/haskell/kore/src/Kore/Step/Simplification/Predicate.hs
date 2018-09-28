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
    ( simplify
    ) where

import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Top_ )
import           Kore.Predicate.Predicate
                 ( Predicate, unwrapPredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns )
import           Kore.Step.PredicateSubstitution
                 ( PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.PredicateSubstitution as PredicateSubstitution
                 ( PredicateSubstitution (..), bottom )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (PureMLPatternSimplifier),
                 Simplifier )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

simplify
    ::  ( MetaOrObject level
        , Show (variable level)
        )
    => PureMLPatternSimplifier level variable
    -> Predicate level variable
    -> Simplifier
        ( PredicateSubstitution level variable
        , SimplificationProof level
        )
simplify (PureMLPatternSimplifier simplifier) predicate = do
    (patternOr, _proof) <- simplifier (unwrapPredicate predicate)
    case OrOfExpandedPattern.extractPatterns patternOr of
        [] -> return
            ( PredicateSubstitution.bottom
            , SimplificationProof
            )
        [ExpandedPattern
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
