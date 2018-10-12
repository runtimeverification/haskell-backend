module Test.Kore.Builtin.List where

import Test.QuickCheck
       ( Property, property, (.&&.), (===) )
import Test.Tasty.HUnit

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.Sentence
import qualified Kore.ASTUtils.SmartConstructors as Kore
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import           Kore.Builtin.Hook
                 ( hookAttribute )
import qualified Kore.Builtin.List as List
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Step.MockSimplifiers as Mock

{- |
    @
        get{}(unit{}(), _) === \bottom{}()
    @
 -}
prop_getUnit :: Integer -> Property
prop_getUnit k =
    let patGet = App_ symbolGet [App_ symbolUnit [], Test.Int.asPattern k]
        predicate = mkEquals mkBottom patGet
    in
        allProperties
            [ ExpandedPattern.bottom === evaluate patGet
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        get{}(concat{}(element{}(e), ...), 0) === e
    @
 -}
prop_getFirstElement :: Seq Integer -> Property
prop_getFirstElement values =
    let patGet = App_ symbolGet [ patList , Test.Int.asPattern 0 ]
        patList = asPattern (Test.Int.asPattern <$> values)
        value =
            case values of
                Seq.Empty -> Nothing
                v Seq.:<| _ -> Just v
        patFirst = maybe mkBottom Test.Int.asPattern value
        predicate = mkEquals patGet patFirst
    in
        allProperties
            [ Test.Int.asPartialExpandedPattern value === evaluate patGet
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        get{}(concat{}(..., element{}(e)), -1) === e
    @
 -}
prop_getLastElement :: Seq Integer -> Property
prop_getLastElement values =
    let patGet = App_ symbolGet [ patList , Test.Int.asPattern (-1) ]
        patList = asPattern (Test.Int.asPattern <$> values)
        value =
            case values of
                Seq.Empty -> Nothing
                _ Seq.:|> v -> Just v
        patFirst = maybe mkBottom Test.Int.asPattern value
        predicate = give testSymbolOrAliasSorts $ mkEquals patGet patFirst
    in
        allProperties
            [ Test.Int.asPartialExpandedPattern value === evaluate patGet
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        concat{}(unit{}(), ...) === concat{}(..., unit{}()) === ...
    @
 -}
prop_concatUnit :: Seq Integer -> Property
prop_concatUnit values =
    let patUnit = App_ symbolUnit []
        patValues = asPattern (Test.Int.asPattern <$> values)
        patConcat1 = App_ symbolConcat [ patUnit, patValues ]
        patConcat2 = App_ symbolConcat [ patValues, patUnit ]
        predicate1 = give testSymbolOrAliasSorts $ mkEquals patValues patConcat1
        predicate2 = give testSymbolOrAliasSorts $ mkEquals patValues patConcat2
    in
        allProperties
            [ evaluate patValues === evaluate patConcat1
            , evaluate patValues === evaluate patConcat2
            , ExpandedPattern.top === evaluate predicate1
            , ExpandedPattern.top === evaluate predicate2
            ]

{- |
    @
        concat{}(concat{}(as : List{}, bs : List{}), cs : List{})
        ===
        concat{}(as : List{}, concat{}(bs : List{}, cs : List{}))
    @
 -}
prop_concatAssociates :: Seq Integer -> Seq Integer -> Seq Integer -> Property
prop_concatAssociates values1 values2 values3 =
    let patList1 = asPattern $ Test.Int.asPattern <$> values1
        patList2 = asPattern $ Test.Int.asPattern <$> values2
        patList3 = asPattern $ Test.Int.asPattern <$> values3
        patConcat12 = App_ symbolConcat [ patList1, patList2 ]
        patConcat23 = App_ symbolConcat [ patList2, patList3 ]
        patConcat12_3 = App_ symbolConcat [ patConcat12, patList3 ]
        patConcat1_23 = App_ symbolConcat [ patList1, patConcat23 ]
        predicate = give testSymbolOrAliasSorts (mkEquals patConcat12_3 patConcat1_23)
    in
        allProperties
            [ evaluate patConcat12_3 === evaluate patConcat1_23
            , ExpandedPattern.top === evaluate predicate
            ]

-- | Check that simplification is carried out on list elements.
unit_simplify :: Assertion
unit_simplify =
    let
        x =
            mkVar Variable
                { variableName = testId "x"
                , variableSort = Test.Int.intSort
                }
        original =
            mkDomainValue listSort
            $ BuiltinDomainList (Seq.fromList [mkAnd x mkTop])
        expected =
            ExpandedPattern.fromPurePattern
            $ mkDomainValue listSort
            $ BuiltinDomainList (Seq.fromList [x])
        actual = evaluate original
    in
        assertEqual "Expected simplified List" expected actual

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asPattern :: List.Builtin Variable -> CommonPurePattern Object
Right asPattern = List.asPattern indexedModule listSort

-- | Specialize 'List.asPattern' to the builtin sort 'listSort'.
asExpandedPattern :: List.Builtin Variable -> CommonExpandedPattern Object
Right asExpandedPattern = List.asExpandedPattern indexedModule listSort

-- | A sort to hook to the builtin @LIST.List@.
listSort :: Sort Object
listSort =
    SortActualSort SortActual
        { sortActualName = testId "List"
        , sortActualSorts = []
        }

-- | Declare 'listSort' in a Kore module.
listSortDecl :: KoreSentence
listSortDecl =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = listSort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "LIST.List" ]
        }
        :: KoreSentenceSort Object)

importInt :: KoreSentence
importInt =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = Test.Int.intModuleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

listModuleName :: ModuleName
listModuleName = ModuleName "LIST"

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: String -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

symbolUnit :: SymbolOrAlias Object
Right symbolUnit = List.lookupSymbolUnit indexedModule

symbolElement :: SymbolOrAlias Object
Right symbolElement = List.lookupSymbolElement indexedModule

symbolConcat :: SymbolOrAlias Object
Right symbolConcat = List.lookupSymbolConcat indexedModule

symbolGet :: SymbolOrAlias Object
Right symbolGet = List.lookupSymbolGet indexedModule

{- | Declare the @LIST@ builtins.
 -}
listModule :: KoreModule
listModule =
    Module
        { moduleName = listModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importInt
            , listSortDecl
            , hookedSymbolDecl "LIST.unit" (builtinSymbol "unitList")
                listSort []
            , hookedSymbolDecl "LIST.element" (builtinSymbol "elementList")
                listSort [Test.Int.intSort]
            , hookedSymbolDecl "LIST.concat" (builtinSymbol "concatList")
                listSort [listSort, listSort]
            , hookedSymbolDecl "LIST.get" (builtinSymbol "getList")
                Test.Int.intSort [listSort, Test.Int.intSort]
            ]
        }

evaluate :: CommonPurePattern Object -> CommonExpandedPattern Object
evaluate pat =
    fst $ evalSimplifier
        $ Pattern.simplify
            tools (Mock.substitutionSimplifier tools) evaluators pat
  where
    tools = extractMetadataTools indexedModule

mapDefinition :: KoreDefinition
mapDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ Test.Bool.boolModule
            , Test.Int.intModule
            , listModule
            ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = verify mapDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup listModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators List.builtinFunctions indexedModule

verify
    :: ParseAttributes a
    => KoreDefinition
    -> Map ModuleName (KoreIndexedModule a)
verify defn =
    either (error . Kore.Error.printError) id
        (verifyAndIndexDefinition attrVerify Builtin.koreVerifiers defn)
  where
    attrVerify = defaultAttributesVerification Proxy

testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } =
    extractMetadataTools indexedModule

allProperties :: [Property] -> Property
allProperties = foldr (.&&.) (property True)

-- * Constructors

mkBottom :: CommonPurePattern Object
mkBottom = Kore.mkBottom

mkEquals
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkEquals = give testSymbolOrAliasSorts Kore.mkEquals

mkAnd
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkAnd = give testSymbolOrAliasSorts Kore.mkAnd

mkTop :: CommonPurePattern Object
mkTop = Kore.mkTop

mkVar :: Variable Object -> CommonPurePattern Object
mkVar = give testSymbolOrAliasSorts Kore.mkVar

mkDomainValue
    :: Sort Object
    -> BuiltinDomain (CommonPurePattern Object)
    -> CommonPurePattern Object
mkDomainValue = give testSymbolOrAliasSorts Kore.mkDomainValue
