{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Syntax.DomainValue
    ( DomainValue (..)
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import Data.Function
import Data.Hashable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Unparser

{-|'DomainValue' corresponds to the @\dv@ branch of the @object-pattern@
syntactic category, which are not yet in the Semantics of K document,
but they should appear in Section 9.1.4 (Patterns) at some point.

'domainValueSort' is the sort of the result.

This represents the encoding of an object constant, e.g. we may use
\dv{Int{}}{"123"} instead of a representation based on constructors,
e.g. succesor(succesor(...succesor(0)...))
-}
data DomainValue sort child = DomainValue
    { domainValueSort  :: !sort
    , domainValueChild :: !child
    }
    deriving (Eq, Foldable, Functor, GHC.Generic, Ord, Show, Traversable)

instance (Hashable sort, Hashable child) => Hashable (DomainValue sort child)

instance (NFData sort, NFData child) => NFData (DomainValue sort child)

instance SOP.Generic (DomainValue sort child)

instance SOP.HasDatatypeInfo (DomainValue sort child)

instance (Debug sort, Debug child) => Debug (DomainValue sort child)

instance
    ( Debug sort, Debug child, Diff sort, Diff child )
    => Diff (DomainValue sort child)

instance Unparse child => Unparse (DomainValue Sort child) where
    unparse DomainValue { domainValueSort, domainValueChild } =
        "\\dv"
        <> parameters [domainValueSort]
        <> arguments [domainValueChild]
    unparse2 DomainValue { domainValueSort, domainValueChild } =
        "\\dv"
        <> parameters2 [domainValueSort]
        <> arguments2 [domainValueChild]

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (DomainValue sort)
  where
    synthetic = domainValueChild
    {-# INLINE synthetic #-}

instance Synthetic Sort (DomainValue Sort) where
    synthetic DomainValue { domainValueSort, domainValueChild } =
        domainValueSort
        & seq (matchSort stringMetaSort domainValueChild)
    {-# INLINE synthetic #-}
