{-|
Module      : Kore.Step.Simplification.Variable
Description : Tools for Variable pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Variable
    ( simplify
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.Pattern
                 ( Conditional (..) )
import qualified Kore.Step.Pattern.Or as Or
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| 'simplify' simplifies a 'Variable' pattern, which means returning
an or containing a term made of that variable.
-}
simplify
    :: (MetaOrObject level, Ord (variable level), SortedVariable variable)
    => variable level
    -> ( Or.Pattern level variable
       , SimplificationProof level
       )
simplify var =
    ( MultiOr.make
        [Conditional
            { term = mkVar var
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
