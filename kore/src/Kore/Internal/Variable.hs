{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Internal.Variable
    ( InternalVariable
    , module Kore.Syntax.ElementVariable
    , module Kore.Syntax.SetVariable
    , module Kore.Syntax.Variable
    ) where

import Kore.Debug
       ( Debug )
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
import Kore.Unparser
       ( Unparse )

-- | 'InternalVariable' is the constraint on internal variable types.
type InternalVariable variable =
    ( Ord variable
    , Debug variable, Show variable, Unparse variable
    , SortedVariable variable
    )
