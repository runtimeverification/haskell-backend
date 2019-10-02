{-|
Module      : Kore.Step.Simplification.CharLiteral
Description : Tools for CharLiteral pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.CharLiteral
    ( simplify
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike as TermLike

{-| 'simplify' simplifies a 'CharLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify :: InternalVariable variable => CharLiteral -> OrPattern variable
simplify (CharLiteral char) =
    OrPattern.fromPattern $ Pattern.fromTermLike $ TermLike.markSimplified $ mkCharLiteral char
