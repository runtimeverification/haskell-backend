{-|
Module      : Kore.Simplification.Forall
Description : Tools for Forall pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Forall
    ( simplify
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Forall (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkForall )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..), toMLPattern )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue, make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

-- TODO: Move Forall up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies an 'Forall' pattern with an 'OrOfExpandedPattern'
child.

Right now this has special cases only for top and bottom children.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => Forall level variable (OrOfExpandedPattern level domain variable)
    ->  ( OrOfExpandedPattern level domain variable
        , SimplificationProof level
        )
simplify
    Forall { forallVariable = variable, forallChild = child }
  =
    simplifyEvaluatedForall variable child

simplifyEvaluatedForall
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => variable level
    -> OrOfExpandedPattern level domain variable
    -> (OrOfExpandedPattern level domain variable, SimplificationProof level)
simplifyEvaluatedForall variable simplified
  | OrOfExpandedPattern.isTrue simplified = (simplified, SimplificationProof)
  | OrOfExpandedPattern.isFalse simplified = (simplified, SimplificationProof)
  | otherwise =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkForall
                variable
                (ExpandedPattern.toMLPattern
                    (OrOfExpandedPattern.toExpandedPattern simplified)
                )
            , predicate = makeTruePredicate
            , substitution = []
            }
        ]
    , SimplificationProof
    )
