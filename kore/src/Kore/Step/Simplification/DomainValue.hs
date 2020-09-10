{-|
Module      : Kore.Step.Simplification.DomainValue
Description : Tools for DomainValue pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.DomainValue
    ( simplify
    ) where

import Prelude.Kore

import Control.Lens as Lens
import Data.Generics.Product
    ( field
    )

import Kore.Internal.Conditional
    ( Conditional
    )
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: forall variable
    .  InternalVariable variable
    => DomainValue Sort (OrPattern variable)
    -> OrPattern variable
simplify builtin@DomainValue { domainValueSort } =
    OrPattern.coerceSort domainValueSort
    . MultiOr.map (fmap (markSimplified . mkDomainValue))
    $ simplifyDomainValue builtin

simplifyDomainValue
    :: InternalVariable variable
    => DomainValue Sort (OrPattern variable)
    -> MultiOr (Conditional variable (DomainValue Sort (TermLike variable)))
simplifyDomainValue _ext@DomainValue { domainValueChild } =
    MultiOr.map
        ( sequenceA
        . flip (Lens.set (field @"domainValueChild")) _ext
        )
        domainValueChild
