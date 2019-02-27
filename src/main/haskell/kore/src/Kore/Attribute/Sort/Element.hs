{-|
Module      : Kore.Attribute.Sort.Element
Description : Element sort attribute
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

-}
module Kore.Attribute.Sort.Element
    ( Element (..)
    , elementId, elementSymbol, elementAttribute
    ) where

import Kore.AST.Kore
import Kore.Attribute.Sort.Element.Element

-- | Kore identifier representing the @element@ attribute symbol.
elementId :: Id Object
elementId = "element"

-- | Kore symbol representing the @element@ attribute.
elementSymbol :: SymbolOrAlias Object
elementSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = elementId
        , symbolOrAliasParams = []
        }

-- | Kore pattern representing the @element@ attribute.
elementAttribute
    :: SymbolOrAlias Object
    -> CommonKorePattern
elementAttribute symbol =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = elementSymbol
            , applicationChildren =
                [ (asCommonKorePattern . ApplicationPattern)
                    Application
                        { applicationSymbolOrAlias = symbol
                        , applicationChildren = []
                        }
                ]
            }
