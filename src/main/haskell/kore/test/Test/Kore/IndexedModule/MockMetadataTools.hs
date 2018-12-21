module Test.Kore.IndexedModule.MockMetadataTools
    ( makeMetadataTools
    , constructorFunctionalAttributes
    , constructorAttributes
    , defaultAttributes
    , functionAttributes
    , functionalAttributes
    , injectiveAttributes
    , sortInjectionAttributes
    ) where

import           Data.Maybe
                 ( fromMaybe )
import qualified Data.Set as Set
import           GHC.Stack
                 ( HasCallStack )

import           Kore.AST.Common
                 ( SymbolOrAlias (..) )
import           Kore.Attribute.Constructor
import           Kore.Attribute.Function
import           Kore.Attribute.Functional
import           Kore.Attribute.Injective
import           Kore.Attribute.SortInjection
import           Kore.IndexedModule.MetadataTools
                 ( HeadType, MetadataTools (MetadataTools) )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Sort
                 ( Sort )
import           Kore.Step.StepperAttributes

makeMetadataTools
    :: [(SymbolOrAlias level, StepperAttributes)]
    -> [(SymbolOrAlias level, HeadType)]
    -> [(Sort level, StepperAttributes)]
    -> [(Sort level, Sort level)]
    -> MetadataTools level StepperAttributes
makeMetadataTools attr headTypes sortTypes isSubsortOf =
    MetadataTools
        { symAttributes = attributesFunction attr
        , symbolOrAliasType = headTypeFunction headTypes
        , sortAttributes = functionAttributesFunction sortTypes
        -- TODO(Vladimir): fix the inconsistency that both 'subsorts' and
        -- 'isSubsortOf' only work with direct (non-transitive) relationships.
        -- For now, we can manually add the relationships for tests.
        , isSubsortOf = \first second -> (first, second) `elem` isSubsortOf
        , subsorts = \sort ->
            Set.fromList . fmap snd . filter ((==) sort . fst) $ isSubsortOf
        }

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

functionAttributesFunction
    :: HasCallStack
    => [(Sort level, StepperAttributes)]
    -> Sort level
    -> StepperAttributes
functionAttributesFunction = caseBasedFunction

caseBasedFunction
    :: (Eq a, Show a, HasCallStack)
    => [(a, b)] -> a -> b
caseBasedFunction cases arg =
    fromMaybe
        (error ("Unknown argument: " ++ show arg))
        (lookup arg cases)

functionAttributes :: StepperAttributes
functionAttributes = defaultAttributes { function = Function True }

functionalAttributes :: StepperAttributes
functionalAttributes = defaultAttributes { functional = Functional True }

constructorAttributes :: StepperAttributes
constructorAttributes =
    defaultStepperAttributes
        { constructor = Constructor True
        , injective = Injective True
        }

constructorFunctionalAttributes :: StepperAttributes
constructorFunctionalAttributes =
    constructorAttributes { functional = Functional True }

injectiveAttributes :: StepperAttributes
injectiveAttributes = defaultAttributes { injective = Injective True }

sortInjectionAttributes :: StepperAttributes
sortInjectionAttributes =
    defaultAttributes
        { injective = Injective True
        , sortInjection = SortInjection True
        }

defaultAttributes :: StepperAttributes
defaultAttributes = defaultStepperAttributes
