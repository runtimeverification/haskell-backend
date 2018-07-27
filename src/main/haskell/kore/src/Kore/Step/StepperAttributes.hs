{-|
Module      : Data.Kore.Step.Step
Description : Single and multiple step execution
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.StepperAttributes
  ( StepperAttributes (..)
  , functionalAttribute
  , functionAttribute
  , constructorAttribute
  ) where

import Data.Default

import Kore.AST.Kore
       (CommonKorePattern)
import Kore.AST.Sentence
       (Attributes (..))
import Kore.Implicit.Attributes
       (keyOnlyAttribute)
import Kore.IndexedModule.IndexedModule
       (ParsedAttributes (..))

-- | Kore pattern representing a constructor attribute
-- Would look something like @constructor{}()@ in ASCII Kore
constructorAttribute :: CommonKorePattern
constructorAttribute = keyOnlyAttribute "constructor"

-- | Kore pattern representing a function attribute
-- Would look something like @function{}()@ in ASCII Kore
functionAttribute :: CommonKorePattern
functionAttribute    = keyOnlyAttribute "function"

-- | Kore pattern representing a functional attribute
-- Would look something like @functional{}()@ in ASCII Kore
functionalAttribute :: CommonKorePattern
functionalAttribute  = keyOnlyAttribute "functional"

-- |Data-structure containing attributes relevant to the Kore Stepper
data StepperAttributes =
    StepperAttributes
    { isFunction    :: Bool
      -- ^ Whether a symbol represents a function
    , isFunctional  :: Bool
      -- ^ Whether a symbol is functional
    , isConstructor :: Bool
      -- ^ Whether a symbol represents a constructor
    }
  deriving (Eq, Show)

instance Default StepperAttributes where
    def = StepperAttributes
        { isFunction    = False
        , isFunctional  = False
        , isConstructor = False
        }

instance ParsedAttributes StepperAttributes where
    parseAttributes (Attributes atts) =
        foldr parseStepperAttribute def atts

parseStepperAttribute
    :: CommonKorePattern
    -> StepperAttributes
    -> StepperAttributes
parseStepperAttribute attr parsedAttrs
    | attr == constructorAttribute = parsedAttrs { isConstructor = True }
    | attr == functionAttribute    = parsedAttrs { isFunction    = True }
    | attr == functionalAttribute  = parsedAttrs { isFunctional  = True }
    | otherwise                    = parsedAttrs
