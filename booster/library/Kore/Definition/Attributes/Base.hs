{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Attributes stored together with different entities in a
@KoreDefinition@.
-}
module Kore.Definition.Attributes.Base (
    DefinitionAttributes (..),
    ModuleAttributes (..),
    AxiomAttributes (..),
    ComputedAxiomAttributes (..),
    SymbolType (..),
    SymbolAttributes (..),
    SortAttributes (..),
    Label,
    Location (..),
    Position (..),
    Priority,
) where

import Control.DeepSeq (NFData (..))
import Data.Hashable (Hashable)
import Data.Text (Text)
import Data.Word (Word8)
import GHC.Generics (Generic)

data DefinitionAttributes = DefinitionAttributes
    {
    }
    -- none needed

    deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)

data ModuleAttributes = ModuleAttributes
    {
    }
    -- none needed

    deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)

{- | Things needed for booster rewrite engine:
  * axiom location (for debug logging and error messages)
  * priority (to order and group axioms by descending priority)
  * label (to implement cut-point support)
-}
data AxiomAttributes = AxiomAttributes
    { location :: Location
    , priority :: Priority -- priorities are <= 200
    , ruleLabel :: Maybe Label
    , simplification :: Bool
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

data ComputedAxiomAttributes = ComputedAxiomAttributes
    { containsAcSymbols, preservesDefinedness :: Bool
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

type Label = Text
type Priority = Word8

data Location = Location
    { file :: Text
    , position :: Position
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

data Position = Position
    { line :: Int
    , column :: Int
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

data SymbolType
    = PartialFunction
    | TotalFunction
    | Constructor
    | SortInjection
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

data SymbolAttributes = SymbolAttributes
    { symbolType :: SymbolType
    , isIdem, isAssoc :: Bool
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

newtype SortAttributes = SortAttributes
    { argCount :: Int
    }
    -- none needed

    deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)
