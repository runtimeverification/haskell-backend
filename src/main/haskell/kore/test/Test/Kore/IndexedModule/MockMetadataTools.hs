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

import           Data.Maybe
                 ( fromMaybe )
import qualified Data.Set as Set

import           Kore.AST.Common
                 ( Sort, SymbolOrAlias (..) )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.Attribute.Constructor
import           Kore.Attribute.Function
import           Kore.Attribute.Functional
import           Kore.Attribute.Injective
import           Kore.Attribute.SortInjection
import           Kore.IndexedModule.MetadataTools
                 ( HeadType, MetadataTools (MetadataTools),
                 SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.StepperAttributes

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
