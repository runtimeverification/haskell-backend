{-|
Module      : Kore.Simplification.Or
Description : Tools for Or pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Or
    (simplify
    ) where

import           Kore.AST.Common
                 ( Or (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( merge )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-|'simplify' simplifies an 'Or' pattern with 'OrOfExpandedPattern'
children by merging the two children.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => Or level (OrOfExpandedPattern level variable)
    ->  ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    Or
        { orFirst = first
        , orSecond = second
        }
  =
    ( OrOfExpandedPattern.merge first second
    , SimplificationProof
    )
