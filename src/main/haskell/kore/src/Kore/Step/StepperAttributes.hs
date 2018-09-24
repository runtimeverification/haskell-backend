{-|
Module      : Kore.Step.StepperAttributes
Description : Attributes used for step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.StepperAttributes
  ( StepperAttributes (..)
  , isFunction_
  , isFunctional_
  , isConstructor_
  , isInjective_
  , isSortInjection_
  , functionalAttribute
  , functionAttribute
  , constructorAttribute
  , injectiveAttribute
  , sortInjectionAttribute
  , hookAttribute
  , convertMetadataTools
  ) where

import Data.Default
import Data.Reflection
       ( Given, given )

import           Kore.AST.Common
                 ( SymbolOrAlias )
import           Kore.AST.Kore
                 ( CommonKorePattern )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Attribute.Parser as Attribute
import           Kore.Builtin.Hook
import           Kore.Implicit.Attributes
                 ( keyOnlyAttribute )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import Kore.SMT.SMT

convertMetadataTools
    :: MetadataTools level StepperAttributes
    -> MetadataTools level SMTAttributes
convertMetadataTools tools = MetadataTools
    { symAttributes  = convert . symAttributes  tools
    , sortAttributes = convert . sortAttributes tools
    , sortTools = sortTools tools
    }
    where convert (StepperAttributes _ _ _ _ _ hook) = SMTAttributes hook

{- | @constructorAttribute@ represents a @constructor@ attribute Kore pattern.

  Kore syntax:
  @
    constructor{}()
  @

 -}
constructorAttribute :: CommonKorePattern
constructorAttribute = keyOnlyAttribute "constructor"

{- | @injectiveAttribute@ represents a @injective@ attribute Kore pattern.

  Kore syntax:
  @
    injective{}()
  @

 -}
injectiveAttribute :: CommonKorePattern
injectiveAttribute = keyOnlyAttribute "injective"

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

{- | @sortInjectionAttribute@ represents a @sortInjection@ attribute Kore pattern.

  Kore syntax:
  @
    sortInjection{}()
  @

 -}
sortInjectionAttribute :: CommonKorePattern
sortInjectionAttribute  = keyOnlyAttribute "sortInjection"

-- |Data-structure containing attributes relevant to the Kore Stepper
data StepperAttributes =
    StepperAttributes
    { isFunction      :: !Bool
      -- ^ Whether a symbol represents a function
    , isFunctional    :: !Bool
      -- ^ Whether a symbol is functional
    , isConstructor   :: !Bool
      -- ^ Whether a symbol represents a constructor
    , isInjective     :: !Bool
      -- ^ Whether a symbol represents an injective function
    , isSortInjection :: !Bool
      -- ^ Whether a symbol is a sort injection
    , hook            :: !Hook
      -- ^ The builtin sort or symbol hooked to a sort or symbol
    }
  deriving (Eq, Show)

defaultStepperAttributes :: StepperAttributes
defaultStepperAttributes =
    StepperAttributes
    { isFunction       = False
    , isFunctional     = False
    , isConstructor    = False
    , isInjective      = False
    , isSortInjection  = False
    , hook             = def
    }

isFunction_
    :: (Given (MetadataTools level StepperAttributes))
    => SymbolOrAlias level
    -> Bool
isFunction_ pHead = isFunction (symAttributes given pHead)

isFunctional_
    :: (Given (MetadataTools level StepperAttributes))
    => SymbolOrAlias level
    -> Bool
isFunctional_ pHead = isFunctional (symAttributes given pHead)

isConstructor_
    :: (Given (MetadataTools level StepperAttributes))
    => SymbolOrAlias level
    -> Bool
isConstructor_ pHead = isConstructor (symAttributes given pHead)

isInjective_
    :: (Given (MetadataTools level StepperAttributes))
    => SymbolOrAlias level
    -> Bool
isInjective_ pHead = isInjective (symAttributes given pHead)

isSortInjection_
    :: (Given (MetadataTools level StepperAttributes))
    => SymbolOrAlias level
    -> Bool
isSortInjection_ pHead = isSortInjection (symAttributes given pHead)

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

{- | Is the @injective@ Kore attribute present?

  It is a parse error if the @injective@ attribute is given any arguments.

  See also: 'injectiveAttribute'

 -}
hasInjectiveAttribute :: Attribute.Parser Bool
hasInjectiveAttribute = Attribute.hasKeyOnlyAttribute "injective"

{- | Is the @sortInjection@ Kore attribute present?

  It is a parse error if the @sortInjection@ attribute is given any arguments.

  See also: 'sortInjectionAttribute'

 -}
hasSortInjectionAttribute :: Attribute.Parser Bool
hasSortInjectionAttribute = Attribute.hasKeyOnlyAttribute "sortInjection"

instance ParseAttributes StepperAttributes where
    attributesParser =
        do
            isFunctional <- hasFunctionalAttribute
            isFunction <- hasFunctionAttribute
            isConstructor <- hasConstructorAttribute
            isSortInjection <- hasSortInjectionAttribute
            isInjective <-
                ((isConstructor || isSortInjection) ||) <$> hasInjectiveAttribute
            hook <- attributesParser
            pure StepperAttributes
                { isFunction, isFunctional, isConstructor
                , isSortInjection, isInjective, hook }
