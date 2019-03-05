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

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Representation.ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

-- TODO: Move Next up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies a 'Next' pattern with an 'OrOfExpandedPattern'
child.

Right now this does not do any actual simplification.
-}
simplify
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Next Object (OrOfExpandedPattern Object variable)
    ->  ( OrOfExpandedPattern Object variable
        , SimplificationProof Object
        )
simplify
    Next { nextChild = child }
  =
    simplifyEvaluated child

simplifyEvaluated
    ::  ( MetaOrObject Object
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => OrOfExpandedPattern Object variable
    -> (OrOfExpandedPattern Object variable, SimplificationProof Object)
simplifyEvaluated simplified =
    ( OrOfExpandedPattern.make
        [ Predicated
            { term =
                mkNext
                    $ ExpandedPattern.toMLPattern
                    $ OrOfExpandedPattern.toExpandedPattern simplified
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
