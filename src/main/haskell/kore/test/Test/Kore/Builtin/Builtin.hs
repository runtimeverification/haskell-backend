module Test.Kore.Builtin.Builtin
    ( hookedSymbolDecl
    ) where

import Kore.AST.Common
import Kore.AST.MetaOrObject
       ( Object )
import Kore.AST.Sentence
import Kore.Builtin.Hook
       ( hookAttribute )


-- | Declare a symbol hooked to the given builtin name.
hookedSymbolDecl
    :: String
    -- ^ builtin name
    -> SymbolOrAlias Object
    -- ^ symbol
    -> Sort Object
    -- ^ result sort
    -> [Sort Object]
    -- ^ argument sorts
    -> KoreSentence
hookedSymbolDecl
    builtinName
    SymbolOrAlias { symbolOrAliasConstructor }
    sentenceSymbolResultSort
    sentenceSymbolSorts
  =
    (asSentence . SentenceHookedSymbol)
        (SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
            :: KoreSentenceSymbol Object
        )
  where
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolOrAliasConstructor
            , symbolParams = []
            }
    sentenceSymbolAttributes = Attributes [ hookAttribute builtinName ]
