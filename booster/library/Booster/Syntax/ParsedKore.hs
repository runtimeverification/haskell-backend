{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Syntax.ParsedKore (
    -- * Parsing
    parseKoreDefinition,
    parseKorePattern,
    parseKoreModule,
    decodeJsonKoreDefinition,
    encodeJsonKoreDefinition,

    -- * Validating and converting
    internalise,

    -- * loading a definition from a file
    loadDefinition,
) where

import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Except (except, runExcept, runExceptT)
import Data.Aeson qualified as Json
import Data.Aeson.Encode.Pretty qualified as Json
import Data.Bifunctor (first)
import Data.ByteString.Lazy (ByteString)
import Data.Map.Strict (Map)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.IO qualified as Text

import Booster.Definition.Base
import Booster.Syntax.Json qualified as KoreJson
import Booster.Syntax.ParsedKore.Base
import Booster.Syntax.ParsedKore.Internalise as Internalise
import Booster.Syntax.ParsedKore.Parser qualified as Parser
import Kore.Syntax.Json.Types (Id (..))

-- Parsing text

{- | Parse a string representing a Kore definition.

@parseKoreDefinition@ returns a 'KoreDefinition' upon success, or a parse error
message otherwise. The input must contain a valid Kore definition and nothing
else.
-}
parseKoreDefinition ::
    -- | Filename used for error messages
    FilePath ->
    -- | The concrete syntax of a valid Kore definition
    Text ->
    Either String ParsedDefinition
parseKoreDefinition = Parser.parseDefinition

{- | Parse a string representing a Kore pattern.

@parseKorePattern@ returns a 'ParsedPattern' upon success, or a parse error
message otherwise. The input must contain a valid Kore pattern and nothing else.
-}
parseKorePattern ::
    -- | Filename used for error messages
    FilePath ->
    -- | The concrete syntax of a valid Kore pattern
    Text ->
    Either String KoreJson.KorePattern
parseKorePattern = Parser.parsePattern

-- | Parse a string representing a Kore module (for add-module)
parseKoreModule ::
    -- | Filename used for error messages
    FilePath ->
    -- | concrete kore syntax of a Kore module
    Text ->
    Either String ParsedModule
parseKoreModule = Parser.parseModule

-- Parsing and encoding Json

{- | Read a Kore definition from Json.

Reads a Kore definition, returning a @ParsedDefinition@ or an error message.
To read a single @KorePattern@, use @Kore.Syntax.Json.decodePattern@.
-}
decodeJsonKoreDefinition :: ByteString -> Either String ParsedDefinition
decodeJsonKoreDefinition = Json.eitherDecode'

{- | Encode a @ParsedDefinition@ as Json

Uses the aeson-pretty encoding for KorePatterns, but no additions for
the additional types.
-}
encodeJsonKoreDefinition :: ParsedDefinition -> ByteString
encodeJsonKoreDefinition = Json.encodePretty' KoreJson.prettyJsonOpts

-- internalising parsed data

internalise :: Maybe Text -> ParsedDefinition -> Either DefinitionError KoreDefinition
internalise mbMainModule definition =
    runExcept $ Internalise.buildDefinitions definition >>= Internalise.lookupModule mainModule
  where
    mainModule = fromMaybe defaultMain mbMainModule
    defaultMain = (last definition.modules).name.getId

{- | Loads Kore definitions from the given file (combined parsing and
internalisation). The map of module names to definitions is returned
so the main module can be changed.
-}
loadDefinition ::
    [Text] -> FilePath -> IO (Either DefinitionError (Map Text KoreDefinition))
loadDefinition indexCells file = runExceptT $ do
    parsedDef <-
        liftIO (Text.readFile file)
            >>= except . first (ParseError . Text.pack) . parseKoreDefinition file
    let parsedDef'
            | null indexCells =
                parsedDef
            | otherwise =
                ParsedDefinition
                    { modules = parsedDef.modules
                    , attributes = [(Id "indexCells", indexCells)]
                    }
    except $ runExcept $ Internalise.buildDefinitions parsedDef'
