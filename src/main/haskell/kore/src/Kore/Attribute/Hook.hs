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

import           Control.DeepSeq
                 ( NFData (..) )
import qualified Control.Monad as Monad
import           Data.Default
                 ( Default (..) )
import           Data.Hashable
                 ( Hashable )
import qualified Data.Maybe as Maybe
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import           GHC.Generics
                 ( Generic )

import           Kore.AST.Common
                 ( Application (..), Id,
                 Pattern (ApplicationPattern, StringLiteralPattern),
                 StringLiteral (..), SymbolOrAlias (..) )
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Sentence
                 ( Attributes )
import           Kore.Attribute.Parser
                 ( ParseAttributes )
import qualified Kore.Attribute.Parser as Parser
import           Kore.Error

newtype Hook = Hook { getHook :: Maybe Text }
  deriving (Eq, Generic, Ord, Read, Show)

{- | The missing @hook@ attribute.

 -}
emptyHook :: Hook
emptyHook = Hook Nothing

instance Default Hook where
    def = emptyHook

instance Hashable Hook

instance NFData Hook

{- | Kore identifier representing a @hook@ attribute symbol.
 -}
hookId :: Id Object
hookId = "hook"

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
hookAttribute :: String  -- ^ hooked function name
              -> CommonKorePattern
hookAttribute builtin =
    (KoreObjectPattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias = hookSymbol
            , applicationChildren = [lit]
            }
  where
    lit = (KoreMetaPattern . StringLiteralPattern) (StringLiteral builtin)

{- | Parse the @hook@ Kore attribute, if present.

  It is a parse error if the @hook@ attribute is not given exactly one literal
  string argument.

  See also: 'hookAttribute'

 -}
instance ParseAttributes Hook where
    parseAttribute =
        withApplication $ \params args (Hook hook) -> do
            Parser.getZeroParams params
            arg <- Parser.getOneArgument args
            StringLiteral name <- Parser.getStringLiteral arg
            Monad.unless (Maybe.isNothing hook) failDuplicate
            return Hook { getHook = Just (Text.pack name) }
      where
        withApplication = Parser.withApplication hookId
        failDuplicate = Parser.failDuplicate hookId

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
