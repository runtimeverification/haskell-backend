{-|
Module      : Data.Kore.Building.Implicit
Description : Builders for symbols and aliases that are implicitly defined in
              Kore.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Building.Implicit where

import           Data.Kore.AST.Common        (Application (..), Id (..), Meta,
                                              Pattern (..), SymbolOrAlias (..))
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts

data MetaNilSortList = MetaNilSortList
instance ProperPattern Meta SortListSort MetaNilSortList where
    asProperPattern _ =
        ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id "#nilSortList"
                , symbolOrAliasParams = []
                }
            , applicationChildren      = []
            }
metaNilSortList :: MetaNilSortList
metaNilSortList = MetaNilSortList
