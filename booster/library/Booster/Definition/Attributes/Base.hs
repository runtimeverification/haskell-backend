{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

Attributes stored together with different entities in a
@KoreDefinition@.
-}
module Booster.Definition.Attributes.Base (
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
    FileSource (..),
    Priority,
    Flag (..),
    pattern IsIdem,
    pattern IsNotIdem,
    pattern IsAssoc,
    pattern IsNotAssoc,
    pattern IsMacroOrAlias,
    pattern IsNotMacroOrAlias,
) where

import Control.DeepSeq (NFData (..))
import Data.Hashable (Hashable)
import Data.String
import Data.Text (Text)
import Data.Word (Word8)
import GHC.Generics (Generic)
import Prettyprinter as Pretty

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
    { location :: Maybe Location
    , priority :: Priority -- priorities are <= 200
    , ruleLabel :: Maybe Label
    , simplification :: Maybe Priority
    , preserving :: Maybe Bool -- this will override the computed attribute
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

data ComputedAxiomAttributes = ComputedAxiomAttributes
    { containsAcSymbols, preservesDefinedness :: Bool
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

type Label = Text

newtype Priority = Priority Word8
    deriving stock (Eq, Ord, Read, Show)
    deriving newtype (Num, NFData)

newtype FileSource = FileSource FilePath
    deriving stock (Eq, Ord, Show)
    deriving newtype (IsString, NFData, Pretty)

data Location = Location
    { file :: FileSource
    , position :: Position
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData)

instance Pretty Location where
    pretty Location{file, position} =
        Pretty.hsep [pretty file, ": ", pretty (position.line, position.column)]

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

newtype Flag (name :: k) = Flag Bool
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

pattern IsIdem, IsNotIdem :: Flag "isIdem"
pattern IsIdem = Flag True
pattern IsNotIdem = Flag False
{-# COMPLETE IsIdem, IsNotIdem #-}

pattern IsAssoc, IsNotAssoc :: Flag "isAssoc"
pattern IsAssoc = Flag True
pattern IsNotAssoc = Flag False
{-# COMPLETE IsAssoc, IsNotAssoc #-}

pattern IsMacroOrAlias, IsNotMacroOrAlias :: Flag "isMacroOrAlias"
pattern IsMacroOrAlias = Flag True
pattern IsNotMacroOrAlias = Flag False
{-# COMPLETE IsMacroOrAlias, IsNotMacroOrAlias #-}

data SymbolAttributes = SymbolAttributes
    { symbolType :: SymbolType
    , isIdem :: Flag "isIdem"
    , isAssoc :: Flag "isAssoc"
    , isMacroOrAlias :: Flag "isMacroOrAlias"
    }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (NFData, Hashable)

newtype SortAttributes = SortAttributes
    { argCount :: Int
    }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (NFData)
