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

import Data.Text (Text)
import Data.Word (Word8)

data DefinitionAttributes = DefinitionAttributes
    {
    }
    -- none needed

    deriving (Eq, Show)

data ModuleAttributes = ModuleAttributes
    {
    }
    -- none needed

    deriving (Eq, Show)

{- | Things needed for booster rewrite engine:
  * axiom location (for debug logging and error messages)
  * priority (to order and group axioms by descending priority)
  * label (to implement cut-point support)
-}
data AxiomAttributes = AxiomAttributes
    { location :: Location
    , priority :: Priority -- priorities are <= 200
    , label :: Maybe Label
    , simplification :: Bool
    }
    deriving stock (Eq, Ord, Show)

data ComputedAxiomAttributes = ComputedAxiomAttributes
    { containsAcSymbols, preservesDefinedness :: Bool
    }
    deriving stock (Eq, Ord, Show)

type Label = Text
type Priority = Word8

data Location = Location
    { file :: FilePath
    , position :: Position
    }
    deriving stock (Eq, Ord, Show)

data Position = Position
    { line :: Int
    , column :: Int
    }
    deriving stock (Eq, Ord, Show)

{- | Things needed for booster rewrite engine:
  * function flag (won't evaluate)
  * total-function flag (for preserve-definedness pass)
  * constructor flag (constructors are indexed)

Any non-free constructors will be known by name (they are built-in) so
this information is not stored in an attribute.
-}
data SymbolType = PartialFunction | TotalFunction | Constructor | SortInjection
    deriving stock (Eq, Show)

data SymbolAttributes = SymbolAttributes
    { symbolType :: SymbolType
    , isIdem, isAssoc :: Bool
    }
    deriving stock (Eq, Show)

newtype SortAttributes = SortAttributes
    { argCount :: Int
    }
    -- none needed

    deriving stock (Eq, Show)
