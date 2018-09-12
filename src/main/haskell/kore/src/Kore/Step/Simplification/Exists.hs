{-|
Module      : Kore.Simplification.Exists
Description : Tools for Exists pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Exists
    ( simplify
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Exists (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkExists )
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

-- TODO: Move Exists up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies an 'Exists' pattern with an 'OrOfExpandedPattern'
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
    => Exists level variable (OrOfExpandedPattern level domain variable)
    ->  ( OrOfExpandedPattern level domain variable
        , ()
        )
simplify
    Exists { existsVariable = variable, existsChild = child }
  =
    simplifyEvaluatedExists variable child

simplifyEvaluatedExists
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Given (SortTools level)
        , Show (variable level)
        , Ord (variable level)
        )
    => variable level
    -> OrOfExpandedPattern level domain variable
    -> (OrOfExpandedPattern level domain variable, ())
simplifyEvaluatedExists variable simplified
  | OrOfExpandedPattern.isTrue simplified = (simplified, ())
  | OrOfExpandedPattern.isFalse simplified = (simplified, ())
  | otherwise =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term = mkExists
                variable
                (ExpandedPattern.toMLPattern
                    (OrOfExpandedPattern.toExpandedPattern simplified)
                )
            , predicate = makeTruePredicate
            , substitution = []
            }
        ]
    , ()
    )
