{-|
Module      : Data.Kore.Step.Step
Description : Single and multiple step execution
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : traian.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Step.StepperAttributes (StepperAttributes (..)) where

import           Data.Default

import           Data.Kore.AST.Sentence                (Attributes (..))
import           Data.Kore.Implicit.Attributes         (KeyValueAttribute (..), attributeToKeyValueAttribute)
import           Data.Kore.IndexedModule.IndexedModule (ParsedAttributes (..))

keyOnlyAttribute :: String -> KeyValueAttribute
keyOnlyAttribute label =
    KeyValueAttribute
    { key = label
    , value = Nothing
    }

constructorAttribute, functionAttribute, functionalAttribute
    :: KeyValueAttribute
constructorAttribute = keyOnlyAttribute "constructor"
functionAttribute    = keyOnlyAttribute "function"
functionalAttribute  = keyOnlyAttribute "functional"

data StepperAttributes =
    StepperAttributes
    { isFunction    :: Bool
    , isFunctional  :: Bool
    , isConstructor :: Bool
    }

instance Default StepperAttributes where
    def = StepperAttributes
        { isFunction    = False
        , isFunctional  = False
        , isConstructor = False
        }

instance ParsedAttributes StepperAttributes where
    parseAttributes (Attributes atts) =
        foldr (parseStepperAttribute . attributeToKeyValueAttribute) def atts

parseStepperAttribute
    :: Maybe KeyValueAttribute
    -> StepperAttributes
    -> StepperAttributes
parseStepperAttribute (Just attr) parsedAttrs
    | attr == constructorAttribute = parsedAttrs { isConstructor = True }
    | attr == functionAttribute    = parsedAttrs { isFunction    = True }
    | attr == functionalAttribute  = parsedAttrs { isFunctional  = True }
    | otherwise                    = parsedAttrs
parseStepperAttribute Nothing parsedAttrs = parsedAttrs
