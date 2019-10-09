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

import qualified Data.Map as Map
import Data.Maybe
    ( fromMaybe
    )
import qualified Data.Set as Set
import GHC.Stack
    ( HasCallStack
    )

import Kore.Attribute.Constructor
import Kore.Attribute.Function
import Kore.Attribute.Functional
import Kore.Attribute.Injective
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Constructors as Attribute
    ( Constructors
    )
import Kore.Attribute.SortInjection
import Kore.Attribute.Symbol
import Kore.IndexedModule.MetadataTools
    ( MetadataTools (MetadataTools)
    , SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataTools as MetadataTools
    ( MetadataTools (..)
    )
import Kore.Internal.ApplicationSorts
    ( ApplicationSorts
    )
import Kore.Sort
    ( Sort
    )
import qualified Kore.Step.SMT.AST as SMT.AST
    ( SmtDeclarations
    )
import Kore.Syntax.Application
    ( SymbolOrAlias (..)
    )
import Kore.Syntax.Id
    ( Id
    )

makeMetadataTools
    :: HasCallStack
    => [(SymbolOrAlias, StepperAttributes)]
    -> [(Sort, Attribute.Sort)]
    -> [(Sort, Sort)]
    -> [(SymbolOrAlias, ApplicationSorts)]
    -> SMT.AST.SmtDeclarations
    -> Map.Map Id Attribute.Constructors
    -> SmtMetadataTools StepperAttributes
makeMetadataTools
    attr sortTypes isSubsortOf sorts declarations sortConstructors
  =
    MetadataTools
        { sortAttributes = caseBasedFunction sortTypes
        -- TODO(Vladimir): fix the inconsistency that both 'subsorts' and
        -- 'isSubsortOf' only work with direct (non-transitive) relationships.
        -- For now, we can manually add the relationships for tests.
        , isSubsortOf = \first second -> (first, second) `elem` isSubsortOf
        , subsorts = \sort ->
            Set.fromList . fmap snd . filter ((==) sort . fst) $ isSubsortOf
        , applicationSorts = caseBasedFunction sorts
        , symbolAttributes =
            caseBasedFunction
                (map
                    (  \(SymbolOrAlias {symbolOrAliasConstructor}, a)
                    -> (symbolOrAliasConstructor, a)
                    )
                    attr
                )
        , isOverloading = const (const False)
        , isOverloaded = const False
        , smtData = declarations
        , sortConstructors
        }

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
    defaultSymbolAttributes
        { constructor = Constructor True }

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
defaultAttributes = defaultSymbolAttributes
