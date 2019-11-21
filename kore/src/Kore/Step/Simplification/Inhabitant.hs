{-|
Module      : Kore.Step.Simplification.Inhabitant
Description : Tools for Inhabitant pattern simplification.
Copyright   : (c) Runtime Verification, 2018
-}
module Kore.Step.Simplification.Inhabitant
    ( simplify
    ) where

import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
    ( markSimplified
    )
import Kore.Step.Simplification.Simplifiable
    ( Simplifiable
    , SimplifiedChildren
    )
import qualified Kore.Step.Simplification.Simplifiable as Simplifiable
    ( fromTermLike
    )

{-| 'simplify' simplifies a 'StringLiteral' pattern, which means returning
an or containing a term made of that literal.
-}
simplify
    :: InternalVariable variable
    => Inhabitant (SimplifiedChildren variable)
    -> Simplifiable variable
simplify Inhabitant { inhSort } =
    Simplifiable.fromTermLike
    $ TermLike.markSimplified
    $ mkInhabitant inhSort
