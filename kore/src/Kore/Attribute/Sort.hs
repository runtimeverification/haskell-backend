{- |
Module      : Kore.Attribute.Sort
Description : Sort sentence attributes
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Attribute.Sort (
    Sort (..),
) where

import Prelude.Kore hiding (
    concat,
 )

import qualified Control.Monad as Monad
import Data.Generics.Product

import Kore.Attribute.Concat
import Kore.Attribute.Element
import Kore.Attribute.Hook
import Kore.Attribute.Parser hiding (
    Sort,
 )
import Kore.Attribute.Smtlib.Smtlib
import Kore.Attribute.Sort.HasDomainValues (
    HasDomainValues,
 )
import Kore.Attribute.Unit

data Sort = Sort
    { -- | The builtin sort hooked to the sort.
      hook :: !Hook
    , -- | The user-defined translation of the sort for SMT.
      smtlib :: !Smtlib
    , -- | The unit symbol associated with the sort.
      unit :: !(Unit SymbolOrAlias)
    , -- | The element symbol associated with the sort.
      element :: !(Element SymbolOrAlias)
    , -- | The concat symbol associated with the sort.
      concat :: !(Concat SymbolOrAlias)
    , -- | whether the sort has domain values
      hasDomainValues :: !HasDomainValues
    }
    deriving (Eq, Generic, Ord, Show)

instance NFData Sort

defaultSortAttributes :: Sort
defaultSortAttributes =
    Sort
        { hook = def
        , smtlib = def
        , unit = def
        , element = def
        , concat = def
        , hasDomainValues = def
        }

-- | See also: 'defaultSortAttributes'
instance Default Sort where
    def = defaultSortAttributes

instance ParseAttributes Sort where
    parseAttribute attr =
        typed @Hook (parseAttribute attr)
            Monad.>=> typed @Smtlib (parseAttribute attr)
            Monad.>=> typed @(Unit SymbolOrAlias) (parseAttribute attr)
            Monad.>=> typed @(Element SymbolOrAlias) (parseAttribute attr)
            Monad.>=> typed @(Concat SymbolOrAlias) (parseAttribute attr)
            Monad.>=> typed @HasDomainValues (parseAttribute attr)

instance From Sort Attributes where
    from =
        mconcat
            . sequence
                [ toAttributes . hook
                , toAttributes . smtlib
                , toAttributes . unit
                , toAttributes . element
                , toAttributes . concat
                , toAttributes . hasDomainValues
                ]
