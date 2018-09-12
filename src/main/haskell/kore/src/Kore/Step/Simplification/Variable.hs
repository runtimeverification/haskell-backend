{-|
Module      : Kore.Simplification.Variable
Description : Tools for Variable pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
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
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )

{-| 'simplify' simplifies a 'Variable' pattern, which means returning
an or containing a term made of that variable.
-}
simplify
    :: MetaOrObject level
    => variable level
    -> ( OrOfExpandedPattern level domain variable
       , ()
       )
simplify var =
    ( OrOfExpandedPattern.make
        [ExpandedPattern
            { term = asPurePattern (VariablePattern var)
            , predicate = makeTruePredicate
            , substitution = []
            }
        ]
    , ()
    )
