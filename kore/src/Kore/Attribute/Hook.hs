{-|
Module      : Data.Attribute.Hook
Description : Representation and parser for hook attributes
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
-}
module Kore.Attribute.Hook
    ( Hook (..)
    , emptyHook
    , hookId, hookSymbol, hookAttribute
    , getHookAttribute
    ) where

import Data.Text
       ( Text )

import           Kore.AST.Kore
import           Kore.AST.Sentence
                 ( Attributes )
import           Kore.Attribute.Hook.Hook
import qualified Kore.Attribute.Parser as Parser
import           Kore.Error

{- | Kore symbol representing the head of a @hook@ attribute.

Kore syntax: @hook{}@

 -}
hookSymbol :: SymbolOrAlias Object
hookSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = hookId
        , symbolOrAliasParams = []
        }

{- | Kore pattern representing a @hook@ attribute

Kore syntax: @hook{}("HOOKED.function")@
@"HOOKED.function"@ is a literal string referring to a known builtin
function.

 -}
hookAttribute :: Text  -- ^ hooked function name
              -> CommonKorePattern
hookAttribute builtin =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = hookSymbol
            , applicationChildren = [lit]
            }
  where
    lit = (asCommonKorePattern . StringLiteralPattern) (StringLiteral builtin)

{- | Look up a required @hook{}()@ attribute from the given attributes.

    It is an error if the attribute is missing.

 -}
getHookAttribute
    :: MonadError (Error e) m
    => Attributes
    -> m Text
getHookAttribute attributes = do
    let parser = Parser.parseAttributes attributes
    hook <- Parser.liftParser parser
    maybe (koreFail "missing hook attribute") return (getHook hook)
