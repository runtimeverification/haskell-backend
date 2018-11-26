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

import           Kore.AST.Common
                 ( Pattern (VariablePattern) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( asPurePattern )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| 'simplify' simplifies a 'Variable' pattern, which means returning
an or containing a term made of that variable.
-}
simplify
    :: (MetaOrObject level, Ord (variable level))
    => variable level
    -> ( OrOfExpandedPattern level variable
       , SimplificationProof level
       )
simplify var =
    ( OrOfExpandedPattern.make
        [Predicated
            { term = asPurePattern (VariablePattern var)
            , predicate = makeTruePredicate
            , substitution = mempty
            }
        ]
    , SimplificationProof
    )
