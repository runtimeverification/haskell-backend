module Test.Kore.IndexedModule.MockMetadataTools
    ( makeMetadataTools
    , makeSortTools
    , constructorFunctionalAttributes
    , constructorAttributes
    , defaultAttributes
    , functionAttributes
    , functionalAttributes
    , injectiveAttributes
    , sortInjectionAttributes
    ) where

import Data.Default
       ( def )
import Data.Maybe
       ( fromMaybe )

import           Kore.AST.Common
                 ( Sort, SymbolOrAlias (..) )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (MetadataTools), SortTools )
import qualified Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (StepperAttributes) )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( StepperAttributes (..) )

makeMetadataTools
    :: SortTools level
    -> [(SymbolOrAlias level, StepperAttributes)]
    -> [(Sort level, Sort level)]
    -> MetadataTools level StepperAttributes
makeMetadataTools sortTools attr isSubsortOf =
    MetadataTools
        { symAttributes = attributesFunction attr
        , sortAttributes = const functionAttributes
        , sortTools = sortTools
        , isSubsortOf = \first second -> (first, second) `elem` isSubsortOf
        }

makeSortTools
    :: [(SymbolOrAlias level, ApplicationSorts level)]
    -> SymbolOrAlias level -> ApplicationSorts level
makeSortTools = caseBasedFunction

attributesFunction
    :: [(SymbolOrAlias level, StepperAttributes)]
    -> SymbolOrAlias level
    -> StepperAttributes
attributesFunction = caseBasedFunction

caseBasedFunction
    :: (Eq a, Show a)
    => [(a, b)] -> a -> b
caseBasedFunction cases arg =
    fromMaybe
        (error ("Unknown argument: " ++ show arg))
        (lookup arg cases)

functionAttributes :: StepperAttributes
functionAttributes = StepperAttributes
    { isConstructor = False
    , isFunctional = False
    , isFunction = True
    , isInjective = False
    , isSortInjection = False
    , hook = def
    }

functionalAttributes :: StepperAttributes
functionalAttributes = StepperAttributes
    { isConstructor = False
    , isFunctional = True
    , isFunction = False
    , isInjective = False
    , isSortInjection = False
    , hook = def
    }

constructorFunctionalAttributes :: StepperAttributes
constructorFunctionalAttributes = StepperAttributes
    { isConstructor = True
    , isFunctional = True
    , isFunction = False
    , isInjective = True
    , isSortInjection = False
    , hook = def
    }

constructorAttributes :: StepperAttributes
constructorAttributes = StepperAttributes
    { isConstructor = True
    , isFunctional = False
    , isFunction = False
    , isInjective = True
    , isSortInjection = False
    , hook = def
    }

injectiveAttributes :: StepperAttributes
injectiveAttributes = StepperAttributes
    { isConstructor = False
    , isFunctional = False
    , isFunction = False
    , isInjective = True
    , isSortInjection = False
    , hook = def
    }

sortInjectionAttributes :: StepperAttributes
sortInjectionAttributes = StepperAttributes
    { isConstructor = False
    , isFunctional = False
    , isFunction = False
    , isInjective = True
    , isSortInjection = True
    , hook = def
    }

defaultAttributes :: StepperAttributes
defaultAttributes = StepperAttributes
    { isConstructor = False
    , isFunctional = False
    , isFunction = False
    , isInjective = False
    , isSortInjection = False
    , hook = def
    }
