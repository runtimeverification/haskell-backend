{-|
Module      : Kore.Attribute.Sort.Concat
Description : Concat sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Concat
    ( Concat (..)
    , concatId, concatSymbol, concatAttribute
    ) where

import Kore.AST.Kore
import Kore.Attribute.Sort.Concat.Concat

-- | Kore identifier representing the @concat@ attribute symbol.
concatId :: Id Object
concatId = "concat"

-- | Kore symbol representing the @concat@ attribute.
concatSymbol :: SymbolOrAlias Object
concatSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = concatId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @concat@ attribute.
concatAttribute
    :: SymbolOrAlias Object
    -> CommonKorePattern
concatAttribute symbol =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = concatSymbol
            , applicationChildren =
                [ (asCommonKorePattern . ApplicationPattern)
                    Application
                        { applicationSymbolOrAlias = symbol
                        , applicationChildren = []
                        }
                ]
            }
