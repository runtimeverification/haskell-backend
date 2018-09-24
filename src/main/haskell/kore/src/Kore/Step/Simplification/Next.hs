{-|
Module      : Kore.Step.Simplification.Next
Description : Tools for Next pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Next
    ( simplify
    ) where

import Data.Reflection
       ( Given )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.ASTUtils.SmartConstructors
                 ( mkNext )
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
                 ( make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

-- TODO: Move Next up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies a 'Next' pattern with an 'OrOfExpandedPattern'
child.

Right now this does not do any actual simplification.
-}
simplify
    ::  ( MetaOrObject Object
        , Given (SortTools Object)
        )
    => Next Object (OrOfExpandedPattern Object Variable)
    ->  ( OrOfExpandedPattern Object Variable
        , SimplificationProof Object
        )
simplify
    Next { nextChild = child }
  =
    simplifyEvaluated child

simplifyEvaluated
    ::  ( MetaOrObject Object
        , Given (SortTools Object)
        )
    => OrOfExpandedPattern Object Variable
    -> (OrOfExpandedPattern Object Variable, SimplificationProof Object)
simplifyEvaluated simplified =
    ( OrOfExpandedPattern.make
        [ ExpandedPattern
            { term =
                mkNext
                    $ ExpandedPattern.toMLPattern
                    $ OrOfExpandedPattern.toExpandedPattern simplified
            , predicate = makeTruePredicate
            , substitution = []
            }
        ]
    , SimplificationProof
    )
