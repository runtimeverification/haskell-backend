module Test.Kore.SMT.SMT where

import Test.QuickCheck
       ( Property, (===) )

import Kore.SMT.SMT

import Test.Kore.Builtin.Int as Int

indexedModules :: Map ModuleName (KoreIndexedModule SMTAttributes)
indexedModules = verify Int.intDefinition

