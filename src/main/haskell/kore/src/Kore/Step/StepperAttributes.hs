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

import Control.Applicative
       ( (<|>) )
import Control.Monad
       ( unless )
import Data.Default
import Data.Functor
       ( ($>) )
import Data.Maybe
       ( isJust )

import           Kore.AST.Common
                 ( Application (..), Pattern (..), StringLiteral (..) )
import           Kore.AST.Kore
                 ( CommonKorePattern, pattern KoreMetaPattern,
                 pattern KoreObjectPattern )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Attribute
import           Kore.Error
                 ( koreFail )
import           Kore.Implicit.Attributes
                 ( attributeHead, keyOnlyAttribute )

{- | Kore pattern representing a @constructor@ attribute

  Kore syntax:
  @
    constructor{}()
  @

 -}
constructorAttribute :: CommonKorePattern
constructorAttribute = keyOnlyAttribute "constructor"

{- | Kore pattern representing a @function@ attribute

  Kore syntax:
  @
    function{}()
  @

 -}
functionAttribute :: CommonKorePattern
functionAttribute    = keyOnlyAttribute "function"

{- | Kore pattern representing a @functional@ attribute

  Kore syntax:
  @
    functional{}()
  @

 -}
functionalAttribute :: CommonKorePattern
functionalAttribute  = keyOnlyAttribute "functional"

{- | Kore pattern representing a @hook@ attribute

  Kore syntax:
  @
    hook{}("HOOKED.function")
  @

 -}
hookAttribute :: String  -- ^ hooked function name
              -> CommonKorePattern
hookAttribute builtin =
    (KoreObjectPattern . ApplicationPattern)
    Application
    { applicationSymbolOrAlias = attributeHead "hook"
    , applicationChildren = [lit]
    }
  where
    lit = (KoreMetaPattern . StringLiteralPattern) (StringLiteral builtin)

-- |Data-structure containing attributes relevant to the Kore Stepper
data StepperAttributes =
    StepperAttributes
    { isFunction    :: Bool
      -- ^ Whether a symbol represents a function
    , isFunctional  :: Bool
      -- ^ Whether a symbol is functional
    , isConstructor :: Bool
      -- ^ Whether a symbol represents a constructor
    , hook          :: Maybe String
      -- ^ The builtin function hooked to a symbol
    }
  deriving (Eq, Show)

instance Default StepperAttributes where
    def = StepperAttributes
        { isFunction    = False
        , isFunctional  = False
        , isConstructor = False
        , hook          = Nothing
        }

{- | Is the @functional@ Kore attribute present?

  It is a parse error if the @functional@ attribute is given any arguments.

  See also: 'functionalAttribute'

 -}
hasFunctionalAttribute :: Attribute.Parser Bool
hasFunctionalAttribute = Attribute.hasKeyAttribute "functional"

{- | Is the @function@ Kore attribute present?

  It is a parse error if the @function@ attribute is given any arguments.

  See also: 'functionAttribute'

 -}
hasFunctionAttribute :: Attribute.Parser Bool
hasFunctionAttribute = Attribute.hasKeyAttribute "function"

{- | Is the @constructor@ Kore attribute present?

  It is a parse error if the @constructor@ attribute is given any arguments.

  See also: 'constructorAttribute'

 -}
hasConstructorAttribute :: Attribute.Parser Bool
hasConstructorAttribute = Attribute.hasKeyAttribute "constructor"

{- | Parse the @hook@ Kore attribute, if present.

  It is a parse error if the @hook@ attribute is not given exactly one literal
  string argument.

  See also: 'hookAttribute'

 -}
getHookAttribute :: Attribute.Parser (Maybe String)
getHookAttribute =
    correctAttribute <|> noAttribute
  where
    correctAttribute = Just <$> Attribute.parseStringAttribute "hook"
    noAttribute = Attribute.assertNoAttribute "hook" $> Nothing

instance ParseAttributes StepperAttributes where
    attributesParser =
        do
            isFunctional <- hasFunctionalAttribute
            isFunction <- hasFunctionAttribute
            isConstructor <- hasConstructorAttribute
            hook <- getHookAttribute
            unless (isJust hook `implies` isFunction)
                (koreFail "hooked symbol must have 'function' attribute")
            pure StepperAttributes {..}
      where
        implies a b = not a || b
