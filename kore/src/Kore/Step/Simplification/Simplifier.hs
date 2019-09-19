{-|
Module      : Kore.Step.Simplification.Simplifier
Description : Builds a simplifier.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.Simplification.Simplifier
    ( create
    ) where

import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.TermLike as TermLike
    ( simplifyToOr
    )

create :: TermLikeSimplifier
create = termLikeSimplifier TermLike.simplifyToOr
