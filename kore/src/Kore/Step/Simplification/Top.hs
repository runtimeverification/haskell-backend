{-|
Module      : Kore.Step.Simplification.Top
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
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| simplifies a Top pattern, which means returning an always-true or.
-}
-- TODO (virgil): Preserve pattern sorts under simplification.
simplify
    :: (MetaOrObject level, Ord (variable level))
    => Top level child
    -> (OrPattern level variable, SimplificationProof level)
simplify _ = (OrPattern.top, SimplificationProof)
