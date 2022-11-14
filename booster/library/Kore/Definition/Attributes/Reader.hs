{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Parsing attributes from @ParsedAttributes@ to different internal
types. The required attribute names and parsers for the expected
values are hard-wired.
-}
module Kore.Definition.Attributes.Reader (
    HasAttributes (..),
) where

import Data.Kind
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Word
import Text.Read (readEither)

-- import Text.Regex.Base
import Text.Regex.PCRE

import Kore.Definition.Attributes.Base
import Kore.Syntax.ParsedKore.Base

-- TODO maybe write a proper applicative parsing framework for these attributes (later)

{- | A class describing all attributes we want to extract from parsed
 entities
-}
class HasAttributes tipe where
    type Attributes tipe :: Type

    extract :: tipe -> Attributes tipe

instance HasAttributes ParsedDefinition where
    type Attributes ParsedDefinition = DefinitionAttributes

    extract _ = DefinitionAttributes

instance HasAttributes ParsedModule where
    type Attributes ParsedModule = ModuleAttributes

    extract _ = ModuleAttributes

instance HasAttributes ParsedAxiom where
    type Attributes ParsedAxiom = AxiomAttributes

    extract ParsedAxiom{attributes} =
        AxiomAttributes
            (Location (attributes .: sourceName) (attributes .: locationName))
            (fromMaybe 50 $ attributes .:? "priority")
            (attributes .:? "label")
            (attributes .! "simplification")

sourceName
    , locationName ::
        Text
sourceName = "org'Stop'kframework'Stop'attributes'Stop'Source"
locationName = "org'Stop'kframework'Stop'attributes'Stop'Location"

instance HasAttributes ParsedSymbol where
    type Attributes ParsedSymbol = SymbolAttributes

    extract ParsedSymbol{attributes} =
        SymbolAttributes
            { isFunction = attributes .! "function" || (attributes .! "functional")
            , isTotal = (attributes .! "functional") || (attributes .! "total")
            , isConstructor = attributes .! "constructor"
            }

instance HasAttributes ParsedSort where
    type Attributes ParsedSort = SortAttributes

    extract ParsedSort{sortVars} =
        SortAttributes
            { argCount = length sortVars
            }

----------------------------------------

extractAttribute :: ReadT a => Text -> ParsedAttributes -> a
extractAttribute name =
    extractAttributeOrDefault (error $ show name <> " not found in attributes") name

(.:) :: ReadT a => ParsedAttributes -> Text -> a
(.:) = flip extractAttribute

extractAttributeOrDefault :: ReadT a => a -> Text -> ParsedAttributes -> a
extractAttributeOrDefault def name attribs =
    maybe def (either error id . readT) $ getAttribute name attribs

(.:?) :: ReadT a => ParsedAttributes -> Text -> Maybe a
attribs .:? name = fmap (either error id . readT) $ getAttribute name attribs

extractFlag :: Text -> ParsedAttributes -> Bool
extractFlag = extractAttributeOrDefault False

(.!) :: ParsedAttributes -> Text -> Bool
(.!) = flip extractFlag

----------------------------------------

-- | Type class providing safe readers for different types
class ReadT a where
    readT :: Maybe Text -> Either String a
    default readT :: Read a => Maybe Text -> Either String a
    readT = maybe (Left "empty") (readEither . Text.unpack)

instance ReadT Word8

-- | Bool instance: presence of the attribute implies 'True'
instance ReadT Bool where
    readT = maybe (Right True) (readEither . Text.unpack)

instance ReadT Text where
    readT = maybe (Left "empty") Right

instance ReadT Position where
    readT = maybe (Left "empty position") readLocationType
      where
        readLocationType :: Text -> Either String Position
        readLocationType input =
            case Text.unpack input =~ locRegex :: (String, String, String, [String]) of
                ("", _match, "", [lineStr, columnStr, _, _]) ->
                    Right $ Position (read lineStr) (read columnStr)
                (unmatched, "", "", []) ->
                    Left $ unmatched <> ": garbled location data"
                other ->
                    error $ "bad regex match result: " <> show other

        natRegex, locRegex :: String
        natRegex = "(0|[1-9][0-9]*)"
        locRegex =
            mconcat
                [ "^Location\\("
                , " *"
                , natRegex
                , ","
                , " *"
                , natRegex
                , ","
                , " *"
                , natRegex
                , ","
                , " *"
                , natRegex
                , "\\)$"
                ]

instance ReadT FilePath
