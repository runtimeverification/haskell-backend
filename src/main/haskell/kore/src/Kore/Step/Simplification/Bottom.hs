{-|
Module      : Kore.Step.Simplification.Bottom
Description : Tools for Bottom pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Bottom
    ( simplify
    ) where

import           Kore.AST.Common
                 ( Bottom (..) )
import           Kore.AST.MetaOrObject
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| simplifies a Bottom pattern, which means returning an always-false or.
-}
simplify
    :: (MetaOrObject level, Ord (variable level))
    => Bottom level child
    -> ( OrOfExpandedPattern level variable
       , SimplificationProof level
       )
simplify Bottom {} =
    (MultiOr.make [], SimplificationProof)
