{-|
Module      : Kore.Simplification.Top
Description : Tools for Top pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Top
    ( simplify
    ) where

import           Kore.AST.Common
                 ( Top (..) )
import           Kore.AST.MetaOrObject
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( top )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| simplifies a Top pattern, which means returning an always-true or.
-}
simplify
    :: MetaOrObject level
    => Top level child
    -> ( OrOfExpandedPattern level variable
       , SimplificationProof level
       )
simplify _ =
    (OrOfExpandedPattern.make [ExpandedPattern.top], SimplificationProof)
