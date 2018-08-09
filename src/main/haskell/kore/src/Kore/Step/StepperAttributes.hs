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

import Control.Monad ( foldM )
import Data.Default

import Kore.AST.Kore
       ( CommonKorePattern )
import Kore.AST.Sentence
       ( Attributes (..) )
import Kore.Attribute.Parser ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Attribute
import Kore.Implicit.Attributes
       ( keyOnlyAttribute )

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

instance ParseAttributes StepperAttributes where
    parseAttributes (Attributes atts) =
        foldM parseStepperAttribute def atts

parseStepperAttribute
    :: StepperAttributes
    -> CommonKorePattern
    -> Attribute.Parser StepperAttributes
parseStepperAttribute parsedAttrs attr
    | attr == constructorAttribute = pure (parsedAttrs { isConstructor = True })
    | attr == functionAttribute    = pure (parsedAttrs { isFunction    = True })
    | attr == functionalAttribute  = pure (parsedAttrs { isFunctional  = True })
    | otherwise                    = pure parsedAttrs
