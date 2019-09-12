{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.Variable
    ( InternalVariable
    , module Kore.Syntax.ElementVariable
    , module Kore.Syntax.SetVariable
    , module Kore.Syntax.Variable
    ) where

import Kore.Debug
    ( Debug
    )
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
import Kore.Unparser
    ( Unparse
    )

{- | 'InternalVariable' is the basic constraint on variable types.

All variable types must implement these constraints, and in practice most
functions which are polymorphic over the variable type require most or all of
these constraints.

 -}
type InternalVariable variable =
    ( Ord variable
    , Debug variable, Show variable, Unparse variable
    , SortedVariable variable
    )
