{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

{-# LANGUAGE TemplateHaskell #-}

module Kore.Syntax.DomainValue where

import Control.DeepSeq
       ( NFData (..) )
import Data.Deriving
       ( makeLiftCompare, makeLiftEq, makeLiftShowsPrec )
import Data.Functor.Classes
import Data.Hashable
import GHC.Generics
       ( Generic )

import Kore.AST.MetaOrObject
import Kore.Sort
import Kore.Unparser
import Template.Tools
       ( newDefinitionGroup )

{-|'DomainValue' corresponds to the @\dv@ branch of the @object-pattern@
syntactic category, which are not yet in the Semantics of K document,
but they should appear in Section 9.1.4 (Patterns) at some point.

Although there is no 'Meta' version of 'DomainValue's, for uniformity,
the 'level' type parameter is used to distiguish between the hypothetical
meta- and object- versions of symbol declarations. It should verify
'MetaOrObject level'.

'domainValueSort' is the sort of the result.

This represents the encoding of an object constant, e.g. we may use
\dv{Int{}}{"123"} instead of a representation based on constructors,
e.g. succesor(succesor(...succesor(0)...))
-}
data DomainValue level domain child = DomainValue
    { domainValueSort  :: !Sort
    , domainValueChild :: !(domain child)
    }
    deriving (Foldable, Functor, Generic, Traversable)

$newDefinitionGroup

instance Eq1 domain => Eq1 (DomainValue level domain) where
    liftEq = $(makeLiftEq ''DomainValue)

instance Ord1 domain => Ord1 (DomainValue level domain) where
    liftCompare = $(makeLiftCompare ''DomainValue)

instance Show1 domain => Show1 (DomainValue level domain) where
    liftShowsPrec = $(makeLiftShowsPrec ''DomainValue)

instance (Eq1 domain, Eq child) => Eq (DomainValue level domain child) where
    (==) = eq1

instance (Ord1 domain, Ord child) => Ord (DomainValue level domain child) where
    compare = compare1

instance (Show1 dom, Show child) => Show (DomainValue lvl dom child) where
    showsPrec = showsPrec1

instance Hashable (domain child) => Hashable (DomainValue level domain child)

instance NFData (domain child) => NFData (DomainValue level domain child)

instance
    (Unparse (domain child), level ~ Object) =>
    Unparse (DomainValue level domain child)
  where
    unparse DomainValue { domainValueChild } = unparse domainValueChild
    unparse2 = unparse
