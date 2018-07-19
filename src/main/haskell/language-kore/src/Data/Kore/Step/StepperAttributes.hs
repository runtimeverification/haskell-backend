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

import           Data.Kore.AST.Kore                    (CommonKorePattern)
import           Data.Kore.AST.Sentence                (Attributes (..))
import           Data.Kore.Implicit.Attributes         (constructorAttribute,
                                                        functionAttribute,
                                                        functionalAttribute)
import           Data.Kore.IndexedModule.IndexedModule (ParsedAttributes (..))

data StepperAttributes =
    StepperAttributes
    { isFunction    :: Bool
    , isFunctional  :: Bool
    , isConstructor :: Bool
    , isHooked      :: Maybe String
    }

instance Default StepperAttributes where
    def = StepperAttributes
        { isFunction = False
        , isFunctional = False
        , isConstructor = False
        , isHooked = Nothing
        }

instance ParsedAttributes StepperAttributes where
    parseAttributes (Attributes atts) = foldr parseStepperAttribute def atts

parseStepperAttribute
    :: Data.Kore.AST.Kore.CommonKorePattern
    -> StepperAttributes
    -> StepperAttributes
parseStepperAttribute attr parsedAttrs
    | attr == constructorAttribute = parsedAttrs { isConstructor = True }
    | attr == functionAttribute = parsedAttrs { isFunction = True }
    | attr == functionalAttribute = parsedAttrs { isFunctional = True }
