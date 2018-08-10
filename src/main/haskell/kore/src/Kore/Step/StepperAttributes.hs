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

hookAttribute :: String -> CommonKorePattern
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

hasFunctionalAttribute :: Attribute.Parser Bool
hasFunctionalAttribute = Attribute.hasKeyAttribute "functional"

hasFunctionAttribute :: Attribute.Parser Bool
hasFunctionAttribute = Attribute.hasKeyAttribute "function"

hasConstructorAttribute :: Attribute.Parser Bool
hasConstructorAttribute = Attribute.hasKeyAttribute "constructor"

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
