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
  , hookAttribute
  ) where

import Data.Default

import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Attribute
import           Kore.Builtin.Hook
import           Kore.Implicit.Attributes
                 ( keyOnlyAttribute )

{- | @constructorAttribute@ represents a @constructor@ attribute Kore pattern.

  Kore syntax:
  @
    constructor{}()
  @

 -}
constructorAttribute :: CommonKorePattern
constructorAttribute = keyOnlyAttribute "constructor"

{- | @functionAttribute@ represents a @function@ attribute Kore pattern.

  Kore syntax:
  @
    function{}()
  @

 -}
functionAttribute :: CommonKorePattern
functionAttribute    = keyOnlyAttribute "function"

{- | @functionalAttribute@ represents a @functional@ attribute Kore pattern.

  Kore syntax:
  @
    functional{}()
  @

 -}
functionalAttribute :: CommonKorePattern
functionalAttribute  = keyOnlyAttribute "functional"

-- |Data-structure containing attributes relevant to the Kore Stepper
data StepperAttributes =
    StepperAttributes
    { isFunction    :: !Bool
      -- ^ Whether a symbol represents a function
    , isFunctional  :: !Bool
      -- ^ Whether a symbol is functional
    , isConstructor :: !Bool
      -- ^ Whether a symbol represents a constructor
    , hook          :: !Hook
      -- ^ The builtin sort or symbol hooked to a sort or symbol
    }
  deriving (Eq, Show)

defaultStepperAttributes :: StepperAttributes
defaultStepperAttributes =
    StepperAttributes
    { isFunction    = False
    , isFunctional  = False
    , isConstructor = False
    , hook          = def
    }

-- | See also: 'defaultStepperAttributes'
instance Default StepperAttributes where
    def = defaultStepperAttributes

{- | Is the @functional@ Kore attribute present?

  It is a parse error if the @functional@ attribute is given any arguments.

  See also: 'functionalAttribute'

 -}
hasFunctionalAttribute :: Attribute.Parser Bool
hasFunctionalAttribute = Attribute.hasKeyOnlyAttribute "functional"

{- | Is the @function@ Kore attribute present?

  It is a parse error if the @function@ attribute is given any arguments.

  See also: 'functionAttribute'

 -}
hasFunctionAttribute :: Attribute.Parser Bool
hasFunctionAttribute = Attribute.hasKeyOnlyAttribute "function"

{- | Is the @constructor@ Kore attribute present?

  It is a parse error if the @constructor@ attribute is given any arguments.

  See also: 'constructorAttribute'

 -}
hasConstructorAttribute :: Attribute.Parser Bool
hasConstructorAttribute = Attribute.hasKeyOnlyAttribute "constructor"

instance ParseAttributes StepperAttributes where
    attributesParser =
        do
            isFunctional <- hasFunctionalAttribute
            isFunction <- hasFunctionAttribute
            isConstructor <- hasConstructorAttribute
            hook <- attributesParser
            pure StepperAttributes {..}
