{-|
Module      : Kore.Building.Implicit
Description : Builders for symbols and aliases that are implicitly defined in
              Kore.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : POSIX
-}
module Kore.Building.Implicit where

import Kore.AST.Common
       ( Application (..), AstLocation (..), Id (..), Pattern (..),
       SymbolOrAlias (..) )
import Kore.AST.MetaOrObject
       ( Meta )
import Kore.Building.Patterns
import Kore.Building.Sorts

data MetaNilSortList = MetaNilSortList
instance ProperPattern Meta SortListSort MetaNilSortList where
    asProperPattern _ =
        ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = Id
                    { getId = "#nilSortList"
                    , idLocation = AstLocationImplicit
                    }
                , symbolOrAliasParams = []
                }
            , applicationChildren      = []
            }
metaNilSortList :: MetaNilSortList
metaNilSortList = MetaNilSortList
