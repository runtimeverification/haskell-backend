{-# LANGUAGE TemplateHaskell #-}

module Control.Exception.TH where

import           Control.Exception
import           Data.Typeable
import           Language.Haskell.TH
import qualified Language.Haskell.TH.Lib as TH

{- | Declare a hierarchical instance of 'Exception'.

Declares that the type @child@ is a hierarchical exception inheriting from
@parent@. The parent name is a /value/ name (quoted with @'@ in Template
Haskell) for a data constructor in case the parent type has multiple
constructors. The child name is a /type/ name (quoted with @''@ in Template
Haskell).

The exception type must be an instance of 'Show' and 'Typeable'.
-}
mkException :: Name  -- ^ parent exception constructor name
            -> Name  -- ^ child exception type name
            -> Q [Dec]
mkException parent child =
  do
    e <- newName "e"
    [d|
      instance Exception $(TH.conT child) where
        toException $(TH.varP e) = toException ($(TH.conE parent) $(TH.varE e))
        fromException f =
          do
            $(TH.conP parent [TH.varP e]) <- fromException f
            cast $(TH.varE e)
        |]
