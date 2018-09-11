{-|
Module      : Kore.Simplification.CharLiteral
Description : Tools for CharLiteral pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.CharLiteral
    ( simplify
    ) where

import           Kore.AST.Common
                 ( CharLiteral (..), Pattern (CharLiteralPattern) )
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
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| 'simplify' simplifies a 'CharLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify
    :: CharLiteral
    -> ( OrOfExpandedPattern Meta variable
       , SimplificationProof Meta
       )
simplify str =
    ( OrOfExpandedPattern.make
        [ExpandedPattern
            { term = asPurePattern (CharLiteralPattern str)
            , predicate = makeTruePredicate
            , substitution = []
            }
        ]
    , SimplificationProof
    )
