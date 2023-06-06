{-# LANGUAGE FlexibleContexts #-}

{- | Utilities for (internalised) definitions and other things

Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Booster.Definition.Util (
    -- * summarising a definition
    Summary (..),
    mkSummary,
    prettySummary,

    -- * where things are
    SourceRef (..),
    HasSourceRef (..),
    sourceRefText,
) where

import Control.Applicative (Alternative (..))
import Control.DeepSeq (NFData (..))
import Data.Bifunctor
import Data.ByteString.Char8 (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.List (partition)
import Data.List.Extra (sortOn)
import Data.Map qualified as Map
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Set qualified as Set
import Data.Text (Text)
import GHC.Generics (Generic)
import GHC.Records (HasField (..))
import Prettyprinter (Doc, Pretty, pretty)
import Prettyprinter qualified as Pretty
import Prettyprinter.Render.String qualified as Pretty (renderString)

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Pattern.Index (TermIndex (..))
import Booster.Prettyprinter
import Booster.Util

data Summary = Summary
    { file :: FilePath
    , modNames, sortNames, symbolNames :: [ByteString]
    , subSorts :: Map.Map ByteString [ByteString]
    , axiomCount, preserveDefinednessCount, containAcSymbolsCount :: Int
    , functionRuleCount, simplificationCount, predicateSimplificationCount :: Int
    , rewriteRules :: Map.Map TermIndex [Location] -- FIXME use Identification type
    , functionRules :: Map.Map TermIndex [Location]
    , simplifications :: Map.Map TermIndex [Location]
    , predicateSimplifications :: Map.Map TermIndex [Location]
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)

mkSummary :: FilePath -> KoreDefinition -> Summary
mkSummary file def =
    Summary
        { file
        , modNames = Map.keys def.modules
        , sortNames = Map.keys def.sorts
        , symbolNames = Map.keys def.symbols
        , subSorts = Map.map (Set.toList . snd) def.sorts
        , axiomCount = length $ concat $ concatMap Map.elems (Map.elems def.rewriteTheory)
        , preserveDefinednessCount =
            length $
                filter (\rule -> null $ rule.computedAttributes.notPreservesDefinednessReasons) $
                    concat $
                        concatMap Map.elems (Map.elems def.rewriteTheory)
        , containAcSymbolsCount =
            length $
                filter (\rule -> rule.computedAttributes.containsAcSymbols) $
                    concat $
                        concatMap Map.elems (Map.elems def.rewriteTheory)
        , functionRuleCount =
            length $ concat $ concatMap Map.elems (Map.elems def.functionEquations)
        , simplificationCount =
            length $ concat $ concatMap Map.elems (Map.elems def.functionEquations)
        , predicateSimplificationCount =
            length $ concat $ concatMap Map.elems (Map.elems def.functionEquations)
        , rewriteRules =
            Map.map (fst . locate . concat . Map.elems) def.rewriteTheory
        , functionRules =
            Map.map (fst . locate . concat . Map.elems) def.functionEquations
        , simplifications =
            Map.map (fst . locate . concat . Map.elems) def.simplifications
        , predicateSimplifications =
            Map.map (fst . locate . concat . Map.elems) def.predicateSimplifications
        }
  where
    -- FIXME use the identification function here
    locate :: HasField "attributes" a AxiomAttributes => [a] -> ([Location], Int)
    locate =
        bimap (map fromJust) length
            . partition isJust
            . map (.attributes.location)

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
                <> ( "Subsorts:"
                        : tableView prettyLabel prettyLabel summary.subSorts
                   )
                <> ( "Rewrite rules by term index:"
                        : tableView prettyTermIndex pretty summary.rewriteRules
                   )
                <> ( "Function equations by term index:"
                        : tableView prettyTermIndex pretty summary.functionRules
                   )
                <> ( "Simplifications by term index:"
                        : tableView prettyTermIndex pretty summary.simplifications
                   )
                <> ( "Predicate simplifications by term index:"
                        : tableView prettyTermIndex pretty summary.predicateSimplifications
                   )
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

data SourceRef
    = Labeled Text
    | Located Location
    | UNKNOWN
    deriving (Eq, Ord, Show)

instance Pretty SourceRef where
    pretty = \case
        Located l -> pretty l
        Labeled l -> pretty l
        UNKNOWN -> "UNKNOWN"

sourceRefText :: HasSourceRef a => a -> Text
sourceRefText = renderOneLineText . pretty . sourceRef

-- | class of entities that have a location or ID to present to users
class HasSourceRef a where
    sourceRef :: a -> SourceRef

instance HasSourceRef AxiomAttributes where
    sourceRef attribs =
        fromMaybe UNKNOWN $
            fmap Labeled attribs.ruleLabel
                <|> fmap Located attribs.location

instance HasSourceRef (RewriteRule a) where
    sourceRef r = sourceRef r.attributes
