{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Syntax.DomainValue (
    DomainValue (..),
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.TopBottom
import Kore.Unparser
import Prelude.Kore
import qualified Pretty

{- |'DomainValue' corresponds to the @\dv@ branch of the @object-pattern@
syntactic category, which are not yet in the Semantics of K document,
but they should appear in Section 9.1.4 (Patterns) at some point.

'domainValueSort' is the sort of the result.

This represents the encoding of an object constant, e.g. we may use
\dv{Int{}}{"123"} instead of a representation based on constructors,
e.g. succesor(succesor(...succesor(0)...))
-}
data DomainValue sort child = DomainValue
    { domainValueSort :: !sort
    , domainValueChild :: !child
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (Functor, Foldable, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse child => Unparse (DomainValue Sort child) where
    unparse DomainValue{domainValueSort, domainValueChild} =
        "\\dv"
            <> parameters [domainValueSort]
            <> Pretty.parens (unparse domainValueChild)

    unparse2 DomainValue{domainValueSort, domainValueChild} =
        "\\dv"
            <> parameters2 [domainValueSort]
            Pretty.<+> unparse domainValueChild

instance Synthetic (FreeVariables variable) (DomainValue sort) where
    synthetic = domainValueChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (DomainValue Sort) where
    synthetic DomainValue{domainValueSort, domainValueChild} =
        domainValueSort
            & seq (matchSort stringMetaSort domainValueChild)
    {-# INLINE synthetic #-}

instance TopBottom a => TopBottom (DomainValue Sort a) where
    isTop _ = False
    isBottom DomainValue{domainValueChild} = isBottom domainValueChild
