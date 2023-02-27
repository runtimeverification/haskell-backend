module Test.Kore.IndexedModule.MockMetadataTools (
    makeMetadataTools,
    constructorTotalAttributes,
    constructorAttributes,
    defaultAttributes,
    functionAttributes,
    totalAttributes,
    injectiveAttributes,
    sortInjectionAttributes,
) where

import Data.Map.Strict qualified as Map
import GHC.Generics qualified as GHC
import Kore.Attribute.Constructor
import Kore.Attribute.Function
import Kore.Attribute.Injective
import Kore.Attribute.Sort qualified as Attribute
import Kore.Attribute.Sort.Constructors qualified as Attribute (
    Constructors,
 )
import Kore.Attribute.SortInjection
import Kore.Attribute.Symbol
import Kore.IndexedModule.MetadataTools (
    ExtractSyntax (..),
    MetadataSyntaxData (..),
    MetadataTools (MetadataTools),
    SmtMetadataTools,
 )
import Kore.IndexedModule.MetadataTools qualified as MetadataTools (
    MetadataTools (..),
 )
import Kore.Internal.ApplicationSorts (
    ApplicationSorts,
 )
import Kore.Rewrite.SMT.AST qualified as SMT.AST (
    SmtDeclarations,
 )
import Kore.Sort (
    Sort,
 )
import Kore.Syntax.Application (
    SymbolOrAlias (..),
 )
import Kore.Syntax.Id (
    Id,
 )
import Prelude.Kore

data MockSyntaxData attributes = MockSyntaxData
    { sortAttributes :: [(Sort, Attribute.Sort)]
    , applicationSorts :: [(SymbolOrAlias, ApplicationSorts)]
    , symbolAttributes :: [(SymbolOrAlias, attributes)]
    }
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)

instance ExtractSyntax MockSyntaxData where
    extractSortAttributes sdata = caseBasedFunction $ sortAttributes sdata
    extractApplicationSorts sdata = caseBasedFunction $ applicationSorts sdata
    extractSymbolAttributes sdata =
        caseBasedFunction
            ( map
                ( \(SymbolOrAlias{symbolOrAliasConstructor}, a) ->
                    (symbolOrAliasConstructor, a)
                )
                (symbolAttributes sdata)
            )

makeMetadataTools ::
    [(SymbolOrAlias, StepperAttributes)] ->
    [(Sort, Attribute.Sort)] ->
    [(SymbolOrAlias, ApplicationSorts)] ->
    SMT.AST.SmtDeclarations ->
    Map.Map Id Attribute.Constructors ->
    SmtMetadataTools StepperAttributes
makeMetadataTools attr sortTypes sorts declarations sortConstructors =
    MetadataTools
        { syntax =
            MetadataSyntaxDataExtension $
                MockSyntaxData
                    { sortAttributes = sortTypes
                    , -- TODO(Vladimir): fix the inconsistency that both 'subsorts' and
                      -- 'isSubsortOf' only work with direct (non-transitive) relationships.
                      -- For now, we can manually add the relationships for tests.
                      applicationSorts = sorts
                    , symbolAttributes = attr
                    }
        , smtData = declarations
        , sortConstructors
        }

caseBasedFunction ::
    (Eq a, Show a, HasCallStack) =>
    [(a, b)] ->
    a ->
    b
caseBasedFunction cases arg =
    fromMaybe
        (error ("Unknown argument: " ++ show arg))
        (lookup arg cases)

functionAttributes :: StepperAttributes
functionAttributes = defaultAttributes{function = Function True}

totalAttributes :: StepperAttributes
totalAttributes = defaultAttributes{total = Total True}

constructorAttributes :: StepperAttributes
constructorAttributes =
    defaultSymbolAttributes
        { constructor = Constructor True
        }

constructorTotalAttributes :: StepperAttributes
constructorTotalAttributes =
    constructorAttributes{total = Total True}

injectiveAttributes :: StepperAttributes
injectiveAttributes = defaultAttributes{injective = Injective True}

sortInjectionAttributes :: StepperAttributes
sortInjectionAttributes =
    defaultAttributes
        { injective = Injective True
        , sortInjection = SortInjection True
        }

defaultAttributes :: StepperAttributes
defaultAttributes = defaultSymbolAttributes
