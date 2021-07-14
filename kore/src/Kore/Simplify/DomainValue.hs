{- |
Module      : Kore.Simplify.DomainValue
Description : Tools for DomainValue pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Simplify.DomainValue (
    simplify,
) where

import Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import Kore.Internal.Conditional (
    Conditional,
 )
import Kore.Internal.MultiOr (
    MultiOr,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

{- | 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify ::
    DomainValue Sort (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify builtin@DomainValue{domainValueSort} =
    OrPattern.coerceSort domainValueSort
        . MultiOr.map (fmap (markSimplified . mkDomainValue))
        $ simplifyDomainValue builtin

simplifyDomainValue ::
    DomainValue Sort (OrPattern RewritingVariableName) ->
    MultiOr
        ( Conditional
            RewritingVariableName
            (DomainValue Sort (TermLike RewritingVariableName))
        )
simplifyDomainValue _ext@DomainValue{domainValueChild} =
    MultiOr.map
        ( sequenceA
            . flip (Lens.set (field @"domainValueChild")) _ext
        )
        domainValueChild
