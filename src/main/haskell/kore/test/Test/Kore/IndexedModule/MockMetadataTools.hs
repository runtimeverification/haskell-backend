module Test.Kore.IndexedModule.MockMetadataTools
    ( makeMetadataTools
    , makeSymbolOrAliasSorts
    , constructorFunctionalAttributes
    , constructorAttributes
    , defaultAttributes
    , functionAttributes
    , functionalAttributes
    , injectiveAttributes
    , sortInjectionAttributes
    ) where

import           Data.Default
                 ( def )
import           Data.Maybe
                 ( fromMaybe )
import qualified Data.Set as Set

import           Kore.AST.Common
                 ( Sort, SymbolOrAlias (..) )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.IndexedModule.MetadataTools
                 ( HeadType, MetadataTools (MetadataTools),
                 SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (StepperAttributes) )
import qualified Kore.Step.StepperAttributes as StepperAttributes
                 ( StepperAttributes (..) )

makeMetadataTools
    :: SymbolOrAliasSorts level
    -> [(SymbolOrAlias level, StepperAttributes)]
    -> [(SymbolOrAlias level, HeadType)]
    -> [(Sort level, Sort level)]
    -> MetadataTools level StepperAttributes
makeMetadataTools symbolOrAliasSorts attr headTypes isSubsortOf =
    MetadataTools
        { symAttributes = attributesFunction attr
        , symbolOrAliasType = headTypeFunction headTypes
        , sortAttributes = const functionAttributes
        , symbolOrAliasSorts = symbolOrAliasSorts
        -- TODO(Vladimir): fix the inconsistency that both 'subsorts' and
        -- 'isSubsortOf' only work with direct (non-transitive) relationships.
        -- For now, we can manually add the relationships for tests.
        , isSubsortOf = \first second -> (first, second) `elem` isSubsortOf
        , subsorts = \sort ->
            Set.fromList . fmap snd . filter ((==) sort . fst) $ isSubsortOf
        }

makeSymbolOrAliasSorts
    :: [(SymbolOrAlias level, ApplicationSorts level)]
    -> SymbolOrAlias level -> ApplicationSorts level
makeSymbolOrAliasSorts = caseBasedFunction

attributesFunction
    :: [(SymbolOrAlias level, StepperAttributes)]
    -> SymbolOrAlias level
    -> StepperAttributes
attributesFunction = caseBasedFunction

headTypeFunction
    :: [(SymbolOrAlias level, HeadType)]
    -> SymbolOrAlias level
    -> HeadType
headTypeFunction = caseBasedFunction

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
