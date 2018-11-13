module Test.Kore.Builtin.String where

import Test.QuickCheck
       ( Property, (===) )
import Test.Tasty
       ( TestTree )

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
import           Kore.Attribute.Hook
                 ( hookAttribute )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.String as String
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified SMT

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Builtin.Int as Test.Int
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

concatSymbol :: SymbolOrAlias Object
concatSymbol = builtinSymbol "concatString"

test_concat :: [TestTree]
test_concat =
    [ testString
        "concat simple"
        concatSymbol
        (asPattern <$> ["foo", "bar"])
        (asExpandedPattern "foobar")
    , testString
        "concat left identity"
        concatSymbol
        (asPattern <$> ["", "bar"])
        (asExpandedPattern "bar")
    , testString
        "concat right identity"
        concatSymbol
        (asPattern <$> ["foo", ""])
        (asExpandedPattern "foo")
    ]

substrSymbol :: SymbolOrAlias Object
substrSymbol = builtinSymbol "substrString"

test_substr :: [TestTree]
test_substr =
    [ testString
        "substr simple"
        substrSymbol
        [asPattern "foobar", Test.Int.asPattern 0, Test.Int.asPattern 6]
        (asExpandedPattern "foobar")
    , testString
        "substr out of bounds"
        substrSymbol
        [asPattern "foobar", Test.Int.asPattern 0, Test.Int.asPattern 10]
        (asExpandedPattern "foobar")
    , testString
        "substr negative start"
        substrSymbol
        [asPattern "foobar", Test.Int.asPattern (-10), Test.Int.asPattern 6]
        (asExpandedPattern "foobar")
    , testString
        "substr negative end"
        substrSymbol
        [asPattern "foobar", Test.Int.asPattern 0, Test.Int.asPattern (-1)]
        (asExpandedPattern "")
    , testString
        "substr actual substring"
        substrSymbol
        [asPattern "foobar", Test.Int.asPattern 0, Test.Int.asPattern 3]
        (asExpandedPattern "foo")
    ]

lengthSymbol :: SymbolOrAlias Object
lengthSymbol = builtinSymbol "lengthString"

test_length :: [TestTree]
test_length =
    [ testString
        "length simple"
        lengthSymbol
        [asPattern "foobar"]
        (Test.Int.asExpandedPattern 6)
    , testString
        "length zero"
        lengthSymbol
        [asPattern ""]
        (Test.Int.asExpandedPattern 0)
    ]

findSymbol :: SymbolOrAlias Object
findSymbol = builtinSymbol "findString"

test_find :: [TestTree]
test_find =
    [ testString
        "find simple"
        findSymbol
        [asPattern "foobar", asPattern "foobar", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 0)
    , testString
        "find subpattern"
        findSymbol
        [asPattern "foobar", asPattern "bar", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 3)
    , testString
        "find empty pattern"
        findSymbol
        [asPattern "foobar", asPattern "", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern 0)
    , testString
        "find negative index"
        findSymbol
        [asPattern "foobar", asPattern "foobar", Test.Int.asPattern (-1)]
        (Test.Int.asExpandedPattern 0)
    , testString
        "find after end of string"
        findSymbol
        [asPattern "foobar", asPattern "bar", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern (-1))
    , testString
        "find pattern that does not exist"
        findSymbol
        [asPattern "foobar", asPattern "nope", Test.Int.asPattern 0]
        (Test.Int.asExpandedPattern (-1))
    ]

string2BaseSymbol :: SymbolOrAlias Object
string2BaseSymbol = builtinSymbol "string2baseString"

test_string2Base :: [TestTree]
test_string2Base =
    -- Decimal
    [ testString
        "string2Base decimal simple"
        string2BaseSymbol
        [asPattern "42", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern 42)
    , testString
        "string2Base decimal negative"
        string2BaseSymbol
        [asPattern "-42", Test.Int.asPattern 10]
        (Test.Int.asExpandedPattern (-42))
    , testString
        "string2Base decimal is bottom"
        string2BaseSymbol
        [asPattern "-42.3", Test.Int.asPattern 10]
        bottom
    , testString
        "string2Base decimal empty string is bottom"
        string2BaseSymbol
        [asPattern "", Test.Int.asPattern 10]
        bottom
    , testString
        "string2Base decimal non-number is bottom"
        string2BaseSymbol
        [asPattern "foobar", Test.Int.asPattern 10]
        bottom
    , testString
        "string2Base decimal from hex is bottom"
        string2BaseSymbol
        [asPattern "baad", Test.Int.asPattern 10]
        bottom

    -- Octal
    , testString
        "string2Base octal simple"
        string2BaseSymbol
        [asPattern "42", Test.Int.asPattern 8]
        (Test.Int.asExpandedPattern 34)
    , testString
        "string2Base octal negative is bottom"
        string2BaseSymbol
        [asPattern "-42", Test.Int.asPattern 8]
        bottom
    , testString
        "string2Base octal is bottom"
        string2BaseSymbol
        [asPattern "-42.3", Test.Int.asPattern 8]
        bottom
    , testString
        "string2Base octal empty string is bottom"
        string2BaseSymbol
        [asPattern "", Test.Int.asPattern 8]
        bottom
    , testString
        "string2Base octal non-number is bottom"
        string2BaseSymbol
        [asPattern "foobar", Test.Int.asPattern 8]
        bottom
    , testString
        "string2Base octal from hex is bottom"
        string2BaseSymbol
        [asPattern "baad", Test.Int.asPattern 8]
        bottom

    -- Hexadecimal
    , testString
        "string2Base hex simple"
        string2BaseSymbol
        [asPattern "42", Test.Int.asPattern 16]
        (Test.Int.asExpandedPattern 66)
    , testString
        "string2Base hex negative is bottom"
        string2BaseSymbol
        [asPattern "-42", Test.Int.asPattern 16]
        bottom
    , testString
        "string2Base hex is bottom"
        string2BaseSymbol
        [asPattern "-42.3", Test.Int.asPattern 16]
        bottom
    , testString
        "string2Base hex empty string is bottom"
        string2BaseSymbol
        [asPattern "", Test.Int.asPattern 16]
        bottom
    , testString
        "string2Base hex non-number is bottom"
        string2BaseSymbol
        [asPattern "foobar", Test.Int.asPattern 16]
        bottom
    , testString
        "string2Base hex from hex is bottom"
        string2BaseSymbol
        [asPattern "baad", Test.Int.asPattern 16]
        (Test.Int.asExpandedPattern 47789)
    ]

string2IntSymbol :: SymbolOrAlias Object
string2IntSymbol = builtinSymbol "string2intString"

test_string2Int :: [TestTree]
test_string2Int =
    [ testString
        "string2Base decimal simple"
        string2IntSymbol
        [asPattern "42"]
        (Test.Int.asExpandedPattern 42)
    , testString
        "string2Int decimal negative"
        string2IntSymbol
        [asPattern "-42"]
        (Test.Int.asExpandedPattern (-42))
    , testString
        "string2Int decimal is bottom"
        string2IntSymbol
        [asPattern "-42.3"]
        bottom
    , testString
        "string2Int decimal empty string is bottom"
        string2IntSymbol
        [asPattern ""]
        bottom
    , testString
        "string2Int decimal non-number is bottom"
        string2IntSymbol
        [asPattern "foobar"]
        bottom
    , testString
        "string2Int decimal from hex is bottom"
        string2IntSymbol
        [asPattern "baad"]
        bottom
    ]

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
            [ importKoreModule Test.Bool.boolModuleName
            , importKoreModule Test.Int.intModuleName
            , stringSortDecl
            , hookedSymbolDecl
                ltSymbol
                Test.Bool.boolSort
                [stringSort, stringSort]
                [hookAttribute "STRING.lt"]
            , hookedSymbolDecl
                concatSymbol
                stringSort
                [stringSort, stringSort]
                [hookAttribute "STRING.concat"]
            , hookedSymbolDecl
                substrSymbol
                stringSort
                [stringSort, Test.Int.intSort, Test.Int.intSort]
                [hookAttribute "STRING.substr"]
            , hookedSymbolDecl
                lengthSymbol
                Test.Int.intSort
                [stringSort]
                [hookAttribute "STRING.length"]
            , hookedSymbolDecl
                findSymbol
                Test.Int.intSort
                [stringSort, stringSort, Test.Int.intSort]
                [hookAttribute "STRING.find"]
            , hookedSymbolDecl
                string2BaseSymbol
                Test.Int.intSort
                [stringSort, Test.Int.intSort]
                [hookAttribute "STRING.string2base"]
            , hookedSymbolDecl
                string2IntSymbol
                Test.Int.intSort
                [stringSort]
                [hookAttribute "STRING.string2int"]
            ]
        }

evaluate :: CommonPurePattern Object -> CommonExpandedPattern Object
evaluate pat =
    fst $ SMT.unsafeRunSMT SMT.defaultConfig $ evalSimplifier
    $ Pattern.simplify tools (Mock.substitutionSimplifier tools) evaluators pat
  where
    tools = extractMetadataTools indexedModule

stringDefinition :: KoreDefinition
stringDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ Test.Bool.boolModule
            , Test.Int.intModule
            , stringModule
            ]
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

testString
    :: String
    -> SymbolOrAlias Object
    -> [CommonPurePattern Object]
    -> CommonExpandedPattern Object
    -> TestTree
testString = testSymbol evaluate
