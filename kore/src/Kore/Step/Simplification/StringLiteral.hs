{-|
Module      : Kore.Step.Simplification.StringLiteral
Description : Tools for StringLiteral pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.StringLiteral
    ( simplify
    ) where

import Kore.Internal.TermLike
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromTermLike
    )

{-| 'simplify' simplifies a 'StringLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify :: InternalVariable variable => StringLiteral -> Simplifiable variable
simplify (StringLiteral str) =
    Simplifiable.fromTermLike $ mkStringLiteral str
