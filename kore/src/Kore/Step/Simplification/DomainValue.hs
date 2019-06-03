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

import Kore.Internal.Conditional
       ( Conditional )
import Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
       ( OrPattern )
import Kore.Internal.TermLike
import Kore.Unparser

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => DomainValue Sort (OrPattern variable)
    -> OrPattern variable
simplify builtin =
    MultiOr.filterOr $ do
        child <- simplifyDomainValue builtin
        return (mkDomainValue <$> child)

simplifyDomainValue
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => DomainValue Sort (OrPattern variable)
    -> MultiOr (Conditional variable (DomainValue Sort (TermLike variable)))
simplifyDomainValue _ext = do
    _ext <- sequence _ext
    return (sequenceA _ext)
