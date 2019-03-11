{-|
Module      : Kore.Domain.Class
Description : Interface to generic domains
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module Kore.Domain.Class where

import qualified Control.Lens as Lens
import           Data.Functor.Const
                 ( Const )
import           Data.Void
                 ( Void )

import Kore.AST.Common
       ( DomainValue )
import Kore.AST.MetaOrObject

class Functor domain => Domain domain where
    -- | View a 'Domain' as a 'DomainValue'.
    lensDomainValue
        ::  forall child1 child2
        .   Lens.Lens
                (domain child1)
                (domain child2)
                (DomainValue Object domain child1)
                (DomainValue Object domain child2)

instance Domain (Const Void) where
    lensDomainValue _ = \case {}
