{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause

@ParsedKore@ models a K definition (set of modules) that has been
parsed (but not validated). It uses the types @KorePattern@ and its
components from the Json interface module, and derives a Json
representation.

See https://github.com/runtimeverification/haskell-backend/blob/master/docs/kore-syntax.md
for a description of the syntax itself.
-}
module Booster.Syntax.ParsedKore.Base (
    module Booster.Syntax.ParsedKore.Base,
) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Text (Text)
import Deriving.Aeson (CustomJSON (..))
import GHC.Generics (Generic)

import Kore.Syntax.Json.Types qualified as Syntax

data ParsedDefinition = ParsedDefinition
    { modules :: [ParsedModule]
    , attributes :: ParsedAttributes
    }
    deriving stock (Eq, Show, Generic)
    deriving (FromJSON, ToJSON) via CustomJSON '[] ParsedDefinition

data ParsedModule = ParsedModule
    { name :: Syntax.Id
    , imports :: [(Syntax.Id, ParsedAttributes)]
    , sorts :: [ParsedSort]
    , symbols :: [ParsedSymbol]
    , aliases :: [ParsedAlias]
    , axioms :: [ParsedAxiom]
    , -- , claims :: [ParsedClaim]
      attributes :: ParsedAttributes
    }
    deriving stock (Eq, Show, Generic)
    deriving (FromJSON, ToJSON) via CustomJSON '[] ParsedModule

data ParsedSort = ParsedSort
    { name :: Syntax.Id
    , sortVars :: [Syntax.Id]
    , isHooked :: Bool
    , attributes :: ParsedAttributes
    }
    deriving stock (Eq, Show, Generic)
    deriving (FromJSON, ToJSON) via CustomJSON '[] ParsedSort

data ParsedSymbol = ParsedSymbol
    { name :: Syntax.Id
    , sortVars :: [Syntax.Id]
    , argSorts :: [Syntax.Sort]
    , sort :: Syntax.Sort
    , isHooked :: Bool
    , attributes :: ParsedAttributes
    }
    deriving stock (Eq, Show, Generic)
    deriving (FromJSON, ToJSON) via CustomJSON '[] ParsedSymbol

data ParsedAlias = ParsedAlias
    { name :: Syntax.Id
    , sortVars :: [Syntax.Id]
    , argSorts :: [Syntax.Sort]
    , sort :: Syntax.Sort
    , args :: [Syntax.Id]
    , rhs :: Syntax.KorePattern
    , attributes :: ParsedAttributes
    }
    deriving stock (Eq, Show, Generic)
    deriving (FromJSON, ToJSON) via CustomJSON '[] ParsedAlias

data ParsedAxiom = ParsedAxiom
    { axiom :: Syntax.KorePattern -- assumed to have certain shape
    -- (not validated here)
    , sortVars :: [Syntax.Id]
    , attributes :: ParsedAttributes
    }
    deriving stock (Eq, Show, Generic)
    deriving (FromJSON, ToJSON) via CustomJSON '[] ParsedAxiom

-- newtype ParsedClaim = ParsedClaim ParsedAxiom

type ParsedAttributes = [(AttributeName, AttributeValue)]
type AttributeName = Syntax.Id
type AttributeValue = Maybe Text

getAttribute :: Text -> ParsedAttributes -> Maybe AttributeValue
getAttribute = lookup . Syntax.Id
