module Test.Kore.Builtin.Set where

import Test.QuickCheck
       ( Property, property, (.&&.), (===), (==>) )

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set

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
import qualified Kore.Builtin.Set as Set
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
        in{}(_, unit{}() === \dv{Bool{}}("false")
    @
 -}
prop_getUnit :: Integer -> Property
prop_getUnit k =
    let patIn = App_ symbolIn [ Test.Int.asPattern k, App_ symbolUnit [] ]
        patFalse = Test.Bool.asPattern False
        predicate = mkEquals patFalse patIn
    in
        allProperties
            [ Test.Bool.asExpandedPattern False === evaluate patIn
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        in{}(e : Int{}, element{}(e : Int{})) === \dv{Bool{}}("true")
    @
 -}
prop_inElement :: Integer -> Property
prop_inElement value =
    let patIn = App_ symbolIn [ patValue , patElement ]
        patElement = App_ symbolElement [ patValue ]
        patValue = Test.Int.asPattern value
        patTrue = Test.Bool.asPattern True
        predicate = mkEquals patIn patTrue
    in
        allProperties
            [ Test.Bool.asExpandedPattern True === evaluate patIn
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        in{}(concat{}(..., element{}(e)), e) === \dv{Bool{}}("true")
    @
 -}
prop_inConcat :: Integer -> Set Integer -> Property
prop_inConcat elem' values =
    let patIn = App_ symbolIn [ patElem , patSet ]
        patSet = asPattern (Set.insert elem' values)
        patElem = Test.Int.asPattern elem'
        patTrue = Test.Bool.asPattern True
        predicate = mkEquals patTrue patIn
    in
        allProperties
            [ Test.Bool.asExpandedPattern True === evaluate patIn
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        concat{}(unit{}(), ...) === concat{}(..., unit{}()) === ...
    @
 -}
prop_concatUnit :: Set Integer -> Property
prop_concatUnit values =
    let patUnit = App_ symbolUnit []
        patValues = asPattern values
        patConcat1 = App_ symbolConcat [ patUnit, patValues ]
        patConcat2 = App_ symbolConcat [ patValues, patUnit ]
        predicate1 = mkEquals patValues patConcat1
        predicate2 = mkEquals patValues patConcat2
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
prop_concatAssociates :: Set Integer -> Set Integer -> Set Integer -> Property
prop_concatAssociates values1 values2 values3 =
    let patSet1 = asPattern values1
        patSet2 = asPattern values2
        patSet3 = asPattern values3
        patConcat12 = App_ symbolConcat [ patSet1, patSet2 ]
        patConcat23 = App_ symbolConcat [ patSet2, patSet3 ]
        patConcat12_3 = App_ symbolConcat [ patConcat12, patSet3 ]
        patConcat1_23 = App_ symbolConcat [ patSet1, patConcat23 ]
        predicate = mkEquals patConcat12_3 patConcat1_23
    in
        allProperties
            [ evaluate patConcat12_3 === evaluate patConcat1_23
            , ExpandedPattern.top === evaluate predicate
            ]

prop_difference :: Set Integer -> Set Integer -> Property
prop_difference set1 set2 =
    let patSet1 = asPattern set1
        patSet2 = asPattern set2
        set3 = Set.difference set1 set2
        patSet3 = asPattern set3
        patDifference = App_ symbolDifference [ patSet1, patSet2 ]
        predicate = mkEquals patSet3 patDifference
    in
        allProperties
            [ evaluate patSet3 === evaluate patDifference
            , ExpandedPattern.top === evaluate predicate
            ]

-- | Sets with symbolic keys are not simplified.
prop_symbolic :: Set String -> Property
prop_symbolic values =
    let patMap =
            asSymbolicPattern
            $ Set.map (mkIntVar . testId) values
    in
        not (Set.null values) ==>
        (ExpandedPattern.fromPurePattern patMap === evaluate patMap)

-- | Construct a pattern for a map which may have symbolic keys.
asSymbolicPattern
    :: Set (CommonPurePattern Object)
    -> CommonPurePattern Object
asSymbolicPattern result =
    foldr applyConcat applyUnit (applyElement <$> Set.toAscList result)
  where
    applyUnit = mkDomainValue setSort $ BuiltinDomainSet Set.empty
    applyElement key = App_ symbolElement [key]
    applyConcat set1 set2 = App_ symbolConcat [set1, set2]

-- | Specialize 'Set.asPattern' to the builtin sort 'setSort'.
asPattern :: Set Integer -> CommonPurePattern Object
Right asPattern = (. Set.map Test.Int.asConcretePattern) <$> Set.asPattern indexedModule setSort

-- | Specialize 'Set.asPattern' to the builtin sort 'setSort'.
asExpandedPattern :: Set.Builtin -> CommonExpandedPattern Object
Right asExpandedPattern = Set.asExpandedPattern indexedModule setSort

-- | A sort to hook to the builtin @SET.Set@.
setSort :: Sort Object
setSort =
    SortActualSort SortActual
        { sortActualName = testId "Set"
        , sortActualSorts = []
        }

-- | Declare 'setSort' in a Kore module.
setSortDecl :: KoreSentence
setSortDecl =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = setSort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "SET.Set" ]
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

importBool :: KoreSentence
importBool =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = Test.Bool.boolModuleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

setModuleName :: ModuleName
setModuleName = ModuleName "SET"

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: String -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

symbolUnit :: SymbolOrAlias Object
Right symbolUnit = Set.lookupSymbolUnit indexedModule

symbolElement :: SymbolOrAlias Object
Right symbolElement = Set.lookupSymbolElement indexedModule

symbolConcat :: SymbolOrAlias Object
Right symbolConcat = Set.lookupSymbolConcat indexedModule

symbolIn :: SymbolOrAlias Object
Right symbolIn = Set.lookupSymbolIn indexedModule

symbolDifference :: SymbolOrAlias Object
Right symbolDifference = Set.lookupSymbolDifference indexedModule

{- | Declare the @SET@ builtins.
 -}
setModule :: KoreModule
setModule =
    Module
        { moduleName = setModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importInt
            , importBool
            , setSortDecl
            , hookedSymbolDecl "SET.unit" (builtinSymbol "unitSet")
                setSort []
            , hookedSymbolDecl "SET.element" (builtinSymbol "elementSet")
                setSort [Test.Int.intSort]
            , hookedSymbolDecl "SET.concat" (builtinSymbol "concatSet")
                setSort [setSort, setSort]
            , hookedSymbolDecl "SET.in" (builtinSymbol "inSet")
                Test.Bool.boolSort [Test.Int.intSort, setSort]
            , hookedSymbolDecl "SET.difference" (builtinSymbol "differenceSet")
                setSort [setSort, setSort]
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
            , setModule
            ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = verify mapDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup setModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators Set.builtinFunctions indexedModule

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
MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } = extractMetadataTools indexedModule

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

mkImplies
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkImplies = give testSymbolOrAliasSorts Kore.mkImplies

mkNot :: CommonPurePattern Object -> CommonPurePattern Object
mkNot = give testSymbolOrAliasSorts Kore.mkNot

mkIntVar :: Id Object -> CommonPurePattern Object
mkIntVar variableName =
    mkVar Variable { variableName, variableSort = Test.Int.intSort }
