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
import qualified Kore.Step.Or as Or
import           Kore.Step.Pattern as Pattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Simplification.Data
                 ( SimplificationProof (..) )

{-| simplifies a Top pattern, which means returning an always-true or.
-}
-- TODO (virgil): Preserve pattern sorts under simplification.
simplify
    :: (MetaOrObject level, Ord (variable level))
    => Top level child
    -> ( Or.Pattern level variable
       , SimplificationProof level
       )
simplify _ =
    (MultiOr.make [Pattern.top], SimplificationProof)
