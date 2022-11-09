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
    SymbolAttributes (..),
    SortAttributes (..),
    Label,
    Location (..),
    Position (..),
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
    , priority :: Word8 -- priorities are <= 200
    , label :: Maybe Label
    , simplification :: Bool
    }
    deriving (Eq, Show)

type Label = Text

data Location = Location
    { file :: FilePath
    , position :: Position
    }
    deriving (Eq, Ord, Show)

data Position = Position
    { line :: Int
    , column :: Int
    }
    deriving (Eq, Ord, Show)

{- | Things needed for booster rewrite engine:
  * function flag (won't evaluate)
  * total-function flag (for preserve-definedness pass)
  * constructor flag (constructors are indexed)

Any non-free constructors will be known by name (they are built-in) so
this information is not stored in an attribute.
-}
data SymbolAttributes = SymbolAttributes
    { isFunction :: Bool
    , isTotal :: Bool
    , isConstructor :: Bool
    }
    deriving (Eq, Show)

newtype SortAttributes = SortAttributes
    { argCount :: Int
    }
    -- none needed

    deriving (Eq, Show)
