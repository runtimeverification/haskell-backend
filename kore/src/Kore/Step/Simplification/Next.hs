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
import           Kore.Step.Pattern
                 ( Conditional (..) )
import qualified Kore.Step.Pattern as Pattern
import qualified Kore.Step.Pattern.Or as Or
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )
import           Kore.Unparser

-- TODO: Move Next up in the other simplifiers or something similar. Note
-- that it messes up top/bottom testing so moving it up must be done
-- immediately after evaluating the children.
{-|'simplify' simplifies a 'Next' pattern with an 'Or.Pattern'
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
    => Next Object (Or.Pattern Object variable)
    ->  ( Or.Pattern Object variable
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
    => Or.Pattern Object variable
    -> (Or.Pattern Object variable, SimplificationProof Object)
simplifyEvaluated simplified =
    ( MultiOr.make
        [ Conditional
            { term =
                mkNext
                $ Pattern.toMLPattern
                $ Or.toExpandedPattern simplified
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
