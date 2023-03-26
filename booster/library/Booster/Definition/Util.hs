{- | Utilities for (internalised) definitions and other things

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Definition.Util (
    Summary (..),
    mkSummary,
    prettySummary,
    decodeLabel,
) where

import Control.DeepSeq (NFData (..))
import Data.Bifunctor (first)
import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.List.Extra (sortOn)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import GHC.Generics (Generic)
import Prettyprinter (Doc, Pretty, pretty)
import Prettyprinter qualified as Pretty
import Prettyprinter.Render.String qualified as Pretty (renderString)

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Pattern.Base (decodeLabel)
import Booster.Pattern.Index (TermIndex (..))
import Booster.Prettyprinter

data Summary = Summary
    { file :: FilePath
    , modNames, sortNames, symbolNames :: [ByteString]
    , subSorts :: Map.Map ByteString [ByteString]
    , axiomCount, preserveDefinednessCount, containAcSymbolsCount :: Int
    , termIndexes :: Map.Map TermIndex [Location]
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
        , termIndexes =
            Map.map (map locate . concat . Map.elems) rewriteTheory
        }
  where
    locate :: RewriteRule -> Location
    locate rule = fromMaybe noLocation rule.attributes.location

    noLocation = Location "no file" $ Position 0 0

prettySummary :: Summary -> String
prettySummary = Pretty.renderString . layoutPrettyUnbounded . pretty

instance Pretty Summary where
    pretty summary =
        Pretty.vsep $
            [ list prettyLabel "Modules" summary.modNames
            , list prettyLabel "Sorts" summary.sortNames
            , list prettyLabel "Symbols" summary.symbolNames
            , "Axioms: " <> pretty summary.axiomCount
            , "Axioms preserving definedness: " <> pretty summary.preserveDefinednessCount
            , "Axioms containing AC symbols: " <> pretty summary.containAcSymbolsCount
            ]
                <> ("Subsorts:" : tableView prettyLabel prettyLabel summary.subSorts)
                <> ("Axioms grouped by term index:" : tableView prettyTermIndex pretty summary.termIndexes)
                <> [mempty]
      where
        tableView :: (k -> Doc a) -> (elem -> Doc a) -> Map.Map k [elem] -> [Doc a]
        tableView keyShower elemShower =
            map (uncurry (list elemShower))
                . sortOn (show . fst)
                . map (first (("- " <>) . keyShower))
                . Map.assocs

        list :: (elem -> Doc a) -> Doc a -> [elem] -> Doc a
        list _ header [] = header <> ": -"
        list f header [x] = header <> ": " <> f x
        list f header xs =
            Pretty.hang 2 . Pretty.vsep $
                (header <> ": " <> pretty (length xs)) : map (("- " <>) . f) xs

        prettyLabel = either error (pretty . BS.unpack) . decodeLabel

        prettyTermIndex Anything = "Anything"
        prettyTermIndex (TopSymbol sym) = prettyLabel sym
        prettyTermIndex None = "None"
