{-|
Module      : Kore.Step.Simplification.Inhabitant
Description : Tools for Inhabitant pattern simplification.
Copyright   : (c) Runtime Verification, 2018
-}
module Kore.Step.Simplification.Inhabitant
    ( simplify
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.OrPattern
                 ( OrPattern )
import           Kore.Step.Pattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| 'simplify' simplifies a 'StringLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify
    :: (MetaOrObject level, Ord (variable level), SortedVariable variable)
    => Sort level
    -> ( OrPattern level variable
       , SimplificationProof level
       )
simplify s =
    ( MultiOr.singleton Conditional
        { term = mkInhabitantPattern s
        , predicate = makeTruePredicate
        , substitution = mempty
        }
    , SimplificationProof
    )
