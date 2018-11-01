module Test.Kore.Builtin.String where

import Test.QuickCheck
       ( Property, (===) )

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Text
                 ( Text )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import           Kore.Builtin.Hook
                 ( hookAttribute )
import qualified Kore.Builtin.String as String
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Step.MockSimplifiers as Mock

-- | Test a comparison operator hooked to the given symbol
propComparison
    :: (String -> String -> Bool)
    -- ^ implementation
    -> SymbolOrAlias Object
    -- ^ symbol
    -> (String -> String -> Property)
propComparison impl symb a b =
    let pat = App_ symb (asPattern <$> [a, b])
    in Test.Bool.asExpandedPattern (impl a b) === evaluate pat

prop_lt :: String -> String -> Property
prop_lt = propComparison (<) ltSymbol

ltSymbol :: SymbolOrAlias Object
ltSymbol = builtinSymbol "ltString"

-- | Another name for asPattern.
stringLiteral :: String -> CommonPurePattern Object
stringLiteral = asPattern

-- | Specialize 'String.asPattern' to the builtin sort 'stringSort'.
asPattern :: String -> CommonPurePattern Object
asPattern = String.asPattern stringSort

-- | Specialize 'String.asConcretePattern' to the builtin sort 'stringSort'.
asConcretePattern :: String -> ConcretePurePattern Object
asConcretePattern = String.asConcretePattern stringSort

-- | Specialize 'String.asExpandedPattern' to the builtin sort 'stringSort'.
asExpandedPattern :: String -> CommonExpandedPattern Object
asExpandedPattern = String.asExpandedPattern stringSort

-- | Specialize 'String.asPartialPattern' to the builtin sort 'stringSort'.
asPartialExpandedPattern :: Maybe String -> CommonExpandedPattern Object
asPartialExpandedPattern = String.asPartialExpandedPattern stringSort

-- | A sort to hook to the builtin @STRING.String@.
stringSort :: Sort Object
stringSort =
    SortActualSort SortActual
        { sortActualName = testId "String"
        , sortActualSorts = []
        }

-- | Declare 'stringSort' in a Kore module.
stringSortDecl :: KoreSentence
stringSortDecl =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = stringSort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "STRING.String" ]
        }
        :: KoreSentenceSort Object)

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

{- | Declare a hooked symbol with two arguments.

  The arguments have sort 'stringSort' and the result is 'Test.Bool.boolSort'.

  -}
comparisonSymbolDecl :: String -> SymbolOrAlias Object -> KoreSentence
comparisonSymbolDecl builtinName symbol =
    hookedSymbolDecl
        builtinName
        symbol
        Test.Bool.boolSort
        [stringSort, stringSort]

importBool :: KoreSentence
importBool =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = Test.Bool.boolModuleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

stringModuleName :: ModuleName
stringModuleName = ModuleName "STRING"

{- | Declare the @STRING@ builtins.
 -}
stringModule :: KoreModule
stringModule =
    Module
        { moduleName = stringModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importBool
            , stringSortDecl
            , comparisonSymbolDecl "STRING.lt" ltSymbol
            ]
        }

evaluate :: CommonPurePattern Object -> CommonExpandedPattern Object
evaluate pat =
    fst $ evalSimplifier
    $ Pattern.simplify tools (Mock.substitutionSimplifier tools) evaluators pat
  where
    tools = extractMetadataTools indexedModule

stringDefinition :: KoreDefinition
stringDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ Test.Bool.boolModule, stringModule ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = verify stringDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup stringModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators String.builtinFunctions indexedModule

verify
    :: ParseAttributes a
    => KoreDefinition
    -> Map ModuleName (KoreIndexedModule a)
verify defn =
    either (error . Kore.Error.printError) id
        (verifyAndIndexDefinition attrVerify Builtin.koreVerifiers defn)
  where
    attrVerify = defaultAttributesVerification Proxy
