{-|
Module      : Kore.Attribute.Sort.Unit
Description : Unit sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Unit
    ( Unit (..)
    , unitId, unitSymbol, unitAttribute
    ) where

import Kore.AST.Kore
import Kore.Attribute.Sort.Unit.Unit

-- | Kore identifier representing the @unit@ attribute symbol.
unitId :: Id Object
unitId = "unit"

-- | Kore symbol representing the @unit@ attribute.
unitSymbol :: SymbolOrAlias Object
unitSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = unitId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @unit@ attribute.
unitAttribute
    :: SymbolOrAlias Object
    -> CommonKorePattern
unitAttribute symbol =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = unitSymbol
            , applicationChildren =
                [ (asCommonKorePattern . ApplicationPattern)
                    Application
                        { applicationSymbolOrAlias = symbol
                        , applicationChildren = []
                        }
                ]
            }
