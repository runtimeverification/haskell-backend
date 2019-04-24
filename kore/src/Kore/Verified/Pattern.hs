{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
 -}
module Kore.Verified.Pattern
    ( Kore.Verified.Pattern.Pattern
    ) where

import           Kore.AST.Pure
import           Kore.AST.Valid
import qualified Kore.Domain.Builtin as Domain

type Pattern =
    PurePattern Object Domain.Builtin Variable (Valid (Variable Object) Object)
