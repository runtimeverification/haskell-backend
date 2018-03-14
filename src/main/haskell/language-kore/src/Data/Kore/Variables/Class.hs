{-# LANGUAGE FlexibleContexts #-}
module Data.Kore.Variables.Class where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore

import           Data.Hashable        (hash)
import           Data.Typeable

class ( Show (var Object), Show (var Meta)
      , Typeable var
      ) => VariableClass var
  where
    -- |Retrieves the sort of the variable
    getVariableSort :: MetaOrObject level => var level -> Sort level
    -- |Computes a hash identifying the variable
    getVariableHash :: MetaOrObject level => var level -> Int

instance VariableClass Variable where
    getVariableSort = variableSort
    getVariableHash = hash . getId . variableName


