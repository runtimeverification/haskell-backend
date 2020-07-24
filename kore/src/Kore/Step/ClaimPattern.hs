{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Step.ClaimPattern
    ( ClaimPattern (..)
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariable
    , RewritingVariableName
    )

-- | Representation of reachability claim types.
data ClaimPattern =
    ClaimPattern
    { left :: !(Pattern RewritingVariableName)
    , existentials :: ![RewritingVariable]
    , right :: !(OrPattern RewritingVariableName)
    }

