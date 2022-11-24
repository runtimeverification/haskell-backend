{- | Utilities for (internalised) definitions and other things

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Definition.Util (
    Summary (..),
    mkSummary,
    prettySummary,
    decodeLabel,
) where

import Control.DeepSeq (NFData (..))
import Data.Map qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Generics (Generic)

import Kore.Definition.Attributes.Base
import Kore.Definition.Base

data Summary = Summary
    { file :: FilePath
    , modNames, sortNames, symbolNames :: [Text]
    , subSorts :: Map.Map Text [Text]
    , axiomCount, preserveDefinednessCount, containAcSymbolsCount :: Int
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)

mkSummary :: FilePath -> KoreDefinition -> Summary
mkSummary file KoreDefinition{modules, sorts, symbols, rewriteTheory} =
    Summary
        { file
        , modNames = Map.keys modules
        , sortNames = Map.keys sorts
        , symbolNames = Map.keys symbols
        , subSorts = Map.map (Set.toList . snd) sorts
        , axiomCount = length $ concat $ concatMap Map.elems (Map.elems rewriteTheory)
        , preserveDefinednessCount =
            length $
                filter (\rule -> rule.computedAttributes.preservesDefinedness) $
                    concat $
                        concatMap Map.elems (Map.elems rewriteTheory)
        , containAcSymbolsCount =
            length $
                filter (\rule -> rule.computedAttributes.containsAcSymbols) $
                    concat $
                        concatMap Map.elems (Map.elems rewriteTheory)
        }

prettySummary :: Summary -> String
prettySummary Summary{modNames, sortNames, symbolNames, subSorts, axiomCount, preserveDefinednessCount, containAcSymbolsCount} =
    Text.unpack $
        Text.unlines $
            [ list "Modules" modNames
            , list "Sorts" sortNames
            , list "Symbols" symbolNames
            , "Axioms: " <> Text.pack (show axiomCount)
            , "Axioms preserving definedness: " <> Text.pack (show preserveDefinednessCount)
            , "Axioms containing AC symbols: " <> Text.pack (show containAcSymbolsCount)
            ]
                <> ("Subsorts:" : map (("- " <>) . uncurry list) (Map.assocs subSorts))
  where
    list header [] = header <> ": -"
    list header [x] = header <> ": " <> decodeLabel' x
    list header xs =
        header
            <> ": "
            <> Text.pack (show $ length xs)
            <> Text.concat (map (("\n  - " <>) . decodeLabel') xs)

    decodeLabel' = either error id . decodeLabel

decodeLabel :: Text -> Either String Text
decodeLabel str
    | Text.null str = Right str
    | "'" `Text.isPrefixOf` str =
        let (encoded, rest) = Text.span (/= '\'') (Text.tail str)
         in (<>) <$> decode encoded <*> decodeLabel (Text.drop 1 rest)
    | otherwise =
        let (notEncoded, rest) = Text.span (/= '\'') str
         in (notEncoded <>) <$> decodeLabel rest
  where
    decode :: Text -> Either String Text
    decode s
        | Text.null s = Right s
        | Text.length code < 4 = Left $ "Bad character code  " <> show code
        | otherwise =
            maybe
                (Left $ "Unknown character code  " <> show code)
                (\c -> (c <>) <$> decode rest)
                (Map.lookup code decodeMap)
      where
        (code, rest) = Text.splitAt 4 s

decodeMap :: Map.Map Text Text
decodeMap =
    Map.fromList
        [ ("Spce", " ")
        , ("Bang", "!")
        , ("Quot", "\"")
        , ("Hash", "#")
        , ("Dolr", "$")
        , ("Perc", "%")
        , ("And-", "&")
        , ("Apos", "'")
        , ("LPar", "(")
        , ("RPar", ")")
        , ("Star", "*")
        , ("Plus", "+")
        , ("Comm", ",")
        , ("Hyph", "-")
        , ("Stop", ".")
        , ("Slsh", "/")
        , ("Coln", ":")
        , ("SCln", ";")
        , ("-LT-", "<")
        , ("Eqls", "=")
        , ("-GT-", ">")
        , ("Ques", "?")
        , ("-AT-", "@")
        , ("LSqB", "[")
        , ("RSqB", "]")
        , ("Bash", "\\")
        , ("Xor-", "^")
        , ("Unds", "_")
        , ("BQuo", "`")
        , ("LBra", "{")
        , ("Pipe", "|")
        , ("RBra", "}")
        , ("Tild", "~")
        ]
