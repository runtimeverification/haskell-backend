{-|
Module      : Kore.Domain.Class
Description : Interface to generic domains
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}

module Kore.Domain.Class where

import Kore.AST.MetaOrObject
import Kore.Sort

class Functor domain => Domain domain where
    -- | The 'Sort' of the given domain value.
    domainSort :: forall child. domain child -> Sort Object
