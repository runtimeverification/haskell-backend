{-|
Module      : Kore.Step.Simplification.Inhabitant
Description : Tools for Inhabitant pattern simplification.
Copyright   : (c) Runtime Verification, 2018
-}
module Kore.Step.Simplification.Inhabitant
    ( simplify
    ) where

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( fromTermLike
    )
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
    ( markSimplified
    )

{-| 'simplify' simplifies a 'StringLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify
    :: InternalVariable variable
    => Inhabitant (OrPattern variable)
    -> Pattern variable
simplify Inhabitant { inhSort } =
    Pattern.fromTermLike
    $ TermLike.markSimplified
    $ mkInhabitant inhSort
