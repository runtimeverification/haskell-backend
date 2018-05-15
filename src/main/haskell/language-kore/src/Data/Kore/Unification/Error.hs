{-|
Module      : Data.Kore.Unification.Error
Description : Utilities for unification errors
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Unification.Error (UnificationError(..)) where

import           Data.Kore.AST.Common

-- |'UnificationError' specifies various error cases encountered during
-- unification
data UnificationError level
    = ConstructorClash (SymbolOrAlias level) (SymbolOrAlias level)
    | SortClash (Sort level) (Sort level)
    | NonConstructorHead (SymbolOrAlias level)
    | NonFunctionalHead (SymbolOrAlias level)
    | NonFunctionalPattern
    | UnsupportedPatterns
    | EmptyPatternList
  deriving (Eq, Show)
