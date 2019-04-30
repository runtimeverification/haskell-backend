{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.DomainValue where

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Data.Deriving as Deriving
import           Data.Functor.Classes
import           Data.Hashable
import           GHC.Generics
                 ( Generic )

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
data DomainValue sort domain child = DomainValue
    { domainValueSort  :: !sort
    , domainValueChild :: !(domain child)
    }
    deriving (Foldable, Functor, Generic, Traversable)

Deriving.deriveEq1 ''DomainValue
Deriving.deriveOrd1 ''DomainValue
Deriving.deriveShow1 ''DomainValue

instance
    (Eq sort, Eq1 domain, Eq child) =>
    Eq (DomainValue sort domain child)
  where
    (==) = eq1

instance
    (Ord sort, Ord1 domain, Ord child) =>
    Ord (DomainValue sort domain child)
  where
    compare = compare1

instance
    (Show sort, Show1 domain, Show child) =>
    Show (DomainValue sort domain child)
  where
    showsPrec = showsPrec1

instance
    (Hashable sort, Hashable (domain child)) =>
    Hashable (DomainValue sort domain child)

instance
    (NFData sort, NFData (domain child)) =>
    NFData (DomainValue sort domain child)

instance
    Unparse (domain child) =>
    Unparse (DomainValue Sort domain child)
  where
    unparse DomainValue { domainValueChild } = unparse domainValueChild
    unparse2 = unparse
