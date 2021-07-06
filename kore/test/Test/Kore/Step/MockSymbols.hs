{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-missing-export-lists #-}

module Test.Kore.Step.MockSymbols where

{- Intended usage:
   * Import qualified.
   * use attributesMapping to build mock MetadataTools.
   * Use things like a, b, c, x, y, z for testing.
   RULES:
   * Everything that does not obey the default rules must be clearly
     specified in the name, e.g. 'constantNotFunctional'.
   * constant symbols are, by default, functional.
   * constant functions are called cf, cg, ch.
   * constant constructors are called a, b, c, ...
   * one-element functions are called f, g, h.
   * constructors are called "constr<n><k>" where n is the arity and k is used
     to differentiate between them (both are one-digit).
   * functional constructors are called "functionalConstr<n><k>"
   * functional symbols are called "functional<n><k>"
   * symbols without any special attribute are called "plain<n><k>"
   * variables are called x, y, z...
-}
import qualified Control.Lens as Lens
import qualified Control.Monad as Monad
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Default as Default
import Data.Generics.Product
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Sup
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import Kore.Attribute.Hook (
    Hook (..),
 )
import Kore.Attribute.Pattern.ConstructorLike (
    isConstructorLike,
 )
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Concat as Attribute
import qualified Kore.Attribute.Sort.Constructors as Attribute (
    Constructors,
 )
import qualified Kore.Attribute.Sort.Element as Attribute
import qualified Kore.Attribute.Sort.Unit as Attribute
import Kore.Attribute.Subsort
import qualified Kore.Attribute.Symbol as Attribute
import Kore.Attribute.Synthetic (
    synthesize,
 )
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Builtin.Int
import qualified Kore.Builtin.KEqual as Builtin.KEqual
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Set as Set
import qualified Kore.Builtin.String as Builtin.String
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import qualified Kore.IndexedModule.OverloadGraph as OverloadGraph
import qualified Kore.IndexedModule.SortGraph as SortGraph
import Kore.Internal.InternalList
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.Symbol hiding (
    isConstructorLike,
    sortInjection,
 )
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
    retractKey,
 )
import qualified Kore.Internal.TermLike as Internal
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
    mkConfigVariable,
    mkEquationVariable,
    mkRuleVariable,
 )
import Kore.Sort
import Kore.Step.Axiom.EvaluationStrategy (
    builtinEvaluation,
 )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier (
    AxiomIdentifier (..),
 )
import qualified Kore.Step.Function.Memo as Memo
import qualified Kore.Step.SMT.AST as SMT
import qualified Kore.Step.SMT.Representation.Resolve as SMT (
    resolve,
 )
import qualified Kore.Step.Simplification.Condition as Simplifier.Condition
import Kore.Step.Simplification.Data (
    Env (Env),
    MonadSimplify,
 )
import qualified Kore.Step.Simplification.Data as SimplificationData.DoNotUse
import Kore.Step.Simplification.InjSimplifier
import Kore.Step.Simplification.OverloadSimplifier
import Kore.Step.Simplification.Simplify (
    BuiltinAndAxiomSimplifierMap,
    ConditionSimplifier,
 )
import qualified Kore.Step.Simplification.SubstitutionSimplifier as SubstitutionSimplifier
import Kore.Syntax.Application
import Kore.Syntax.Variable
import Prelude.Kore
import qualified SMT.AST as SMT
import qualified SMT.SimpleSMT as SMT
import qualified Test.ConsistentKore as ConsistentKore (
    CollectionSorts (..),
    Setup (..),
 )
import Test.Kore (
    testId,
 )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

aId :: Id
aId = testId "a"
aSort0Id :: Id
aSort0Id = testId "aSort0"
aSort1Id :: Id
aSort1Id = testId "aSort1"
aSubsortId :: Id
aSubsortId = testId "aSubsort"
aSubOthersortId :: Id
aSubOthersortId = testId "aSubOthersort"
aSubSubsortId :: Id
aSubSubsortId = testId "aSubSubsort"
aTopSortId :: Id
aTopSortId = testId "aTopSort"
aOtherSortId :: Id
aOtherSortId = testId "aOtherSort"
bId :: Id
bId = testId "b"
bSort0Id :: Id
bSort0Id = testId "bSort0"
cId :: Id
cId = testId "c"
dId :: Id
dId = testId "d"
eId :: Id
eId = testId "e"
fId :: Id
fId = testId "f"
fMapId :: Id
fMapId = testId "fMap"
fSort0Id :: Id
fSort0Id = testId "fSort0"
gId :: Id
gId = testId "g"
gSort0Id :: Id
gSort0Id = testId "gSort0"
hId :: Id
hId = testId "h"
cfId :: Id
cfId = testId "cf"
cfSort0Id :: Id
cfSort0Id = testId "cfSort0"
cfSort1Id :: Id
cfSort1Id = testId "cfSort1"
cgId :: Id
cgId = testId "cg"
cgSort0Id :: Id
cgSort0Id = testId "cgSort0"
chId :: Id
chId = testId "ch"
fSetId :: Id
fSetId = testId "fSet"
fIntId :: Id
fIntId = testId "fInt"
fBoolId :: Id
fBoolId = testId "fBool"
fStringId :: Id
fStringId = testId "fString"
fTestIntId :: Id
fTestIntId = testId "fTestInt"
fTestFunctionalIntId :: Id
fTestFunctionalIntId = testId "fTestFunctionalInt"
plain00Id :: Id
plain00Id = testId "plain00"
plain00Sort0Id :: Id
plain00Sort0Id = testId "plain00Sort0"
plain00SubsortId :: Id
plain00SubsortId = testId "plain00Subsort"
plain00OtherSortId :: Id
plain00OtherSortId = testId "plain00OtherSort"
plain00SubSubsortId :: Id
plain00SubSubsortId = testId "plain00SubSubsort"
plain10Id :: Id
plain10Id = testId "plain10"
plain11Id :: Id
plain11Id = testId "plain11"
plain20Id :: Id
plain20Id = testId "plain20"
constr00Id :: Id
constr00Id = testId "constr00"
constr10Id :: Id
constr10Id = testId "constr10"
constr11Id :: Id
constr11Id = testId "constr11"
constr20Id :: Id
constr20Id = testId "constr20"
constrFunct20TestMapId :: Id
constrFunct20TestMapId = testId "constrFunct20TestMap"
function20MapTestId :: Id
function20MapTestId = testId "function20MapTest"
functional00Id :: Id
functional00Id = testId "functional00"
functional01Id :: Id
functional01Id = testId "functional01"
functional10Id :: Id
functional10Id = testId "functional10"
functional11Id :: Id
functional11Id = testId "functional11"
functional20Id :: Id
functional20Id = testId "functional20"
functional00SubSubSortId :: Id
functional00SubSubSortId = testId "functional00SubSubSort"
functionalInjective00Id :: Id
functionalInjective00Id = testId "functionalInjective00"
functionalConstr10Id :: Id
functionalConstr10Id = testId "functionalConstr10"
functionalConstr11Id :: Id
functionalConstr11Id = testId "functionalConstr11"
functionalConstr12Id :: Id
functionalConstr12Id = testId "functionalConstr12"
functionalConstr20Id :: Id
functionalConstr20Id = testId "functionalConstr20"
functionalConstr21Id :: Id
functionalConstr21Id = testId "functionalConstr21"
functionalConstr30Id :: Id
functionalConstr30Id = testId "functionalConstr30"
functionalTopConstr20Id :: Id
functionalTopConstr20Id = testId "functionalTopConstr20"
functionalTopConstr21Id :: Id
functionalTopConstr21Id = testId "functionalTopConstr21"
injective10Id :: Id
injective10Id = testId "injective10"
injective11Id :: Id
injective11Id = testId "injective11"
sortInjectionId :: Id
sortInjectionId = testId "sortInjection"
unitMapId :: Id
unitMapId = testId "unitMap"
elementMapId :: Id
elementMapId = testId "elementMap"
concatMapId :: Id
concatMapId = testId "concatMap"
opaqueMapId :: Id
opaqueMapId = testId "opaqueMap"
inKeysMapId :: Id
inKeysMapId = testId "inKeys"
lessIntId :: Id
lessIntId = testId "lessIntId"
greaterEqIntId :: Id
greaterEqIntId = testId "greaterEqIntId"
tdivIntId :: Id
tdivIntId = testId "tdivIntId"
concatListId :: Id
concatListId = testId "concatList"
elementListId :: Id
elementListId = testId "elementList"
unitListId :: Id
unitListId = testId "unitList"
concatSetId :: Id
concatSetId = testId "concatSet"
opaqueSetId :: Id
opaqueSetId = testId "opaqueSet"
elementSetId :: Id
elementSetId = testId "elementSet"
unitSetId :: Id
unitSetId = testId "unitSet"
keqBoolId :: Id
keqBoolId = testId "keqBool"
sigmaId :: Id
sigmaId = testId "sigma"
anywhereId :: Id
anywhereId = testId "anywhere"
subsubOverloadId :: Id
subsubOverloadId = testId "subsubOverload"
subOverloadId :: Id
subOverloadId = testId "subOverload"
otherOverloadId :: Id
otherOverloadId = testId "otherOverload"
topOverloadId :: Id
topOverloadId = testId "topOverload"
functionSMTId :: Id
functionSMTId = testId "functionSMT"
functionalSMTId :: Id
functionalSMTId = testId "functionalSMT"

symbol :: Id -> [Sort] -> Sort -> Symbol
symbol name operands result =
    Symbol
        { symbolConstructor = name
        , symbolParams = []
        , symbolAttributes = Default.def
        , symbolSorts = applicationSorts operands result
        }

aSymbol :: Symbol
aSymbol = symbol aId [] testSort & functional & constructor

aSort0Symbol :: Symbol
aSort0Symbol = symbol aSort0Id [] testSort0 & functional & constructor

aSort1Symbol :: Symbol
aSort1Symbol = symbol aSort1Id [] testSort1 & functional & constructor

aSubsortSymbol :: Symbol
aSubsortSymbol = symbol aSubsortId [] subSort & functional & constructor

aSubOthersortSymbol :: Symbol
aSubOthersortSymbol =
    symbol aSubOthersortId [] subOthersort & functional & constructor

aSubSubsortSymbol :: Symbol
aSubSubsortSymbol =
    symbol aSubSubsortId [] subSubsort & functional & constructor

aTopSortSymbol :: Symbol
aTopSortSymbol = symbol aTopSortId [] topSort & functional & constructor

aOtherSortSymbol :: Symbol
aOtherSortSymbol = symbol aOtherSortId [] otherSort & functional & constructor

bSymbol :: Symbol
bSymbol = symbol bId [] testSort & functional & constructor

bSort0Symbol :: Symbol
bSort0Symbol = symbol bSort0Id [] testSort0 & functional & constructor

cSymbol :: Symbol
cSymbol = symbol cId [] testSort & functional & constructor

dSymbol :: Symbol
dSymbol = symbol dId [] testSort & functional & constructor

eSymbol :: Symbol
eSymbol = symbol eId [] testSort & functional & constructor

fSymbol :: Symbol
fSymbol = symbol fId [testSort] testSort & function

fSort0Symbol :: Symbol
fSort0Symbol = symbol fSort0Id [testSort0] testSort0 & function

gSymbol :: Symbol
gSymbol = symbol gId [testSort] testSort & function

gSort0Symbol :: Symbol
gSort0Symbol = symbol gSort0Id [testSort0] testSort0 & function

hSymbol :: Symbol
hSymbol = symbol hId [testSort] testSort & function

cfSymbol :: Symbol
cfSymbol = symbol cfId [] testSort & function

cfSort0Symbol :: Symbol
cfSort0Symbol = symbol cfSort0Id [] testSort0 & function

cfSort1Symbol :: Symbol
cfSort1Symbol = symbol cfSort1Id [] testSort1 & function

cgSymbol :: Symbol
cgSymbol = symbol cgId [] testSort & function

cgSort0Symbol :: Symbol
cgSort0Symbol = symbol cgSort0Id [] testSort0 & function

chSymbol :: Symbol
chSymbol = symbol chId [] testSort & function

fSetSymbol :: Symbol
fSetSymbol = symbol fSetId [setSort] setSort & function

fIntSymbol :: Symbol
fIntSymbol = symbol fIntId [intSort] intSort & function

fBoolSymbol :: Symbol
fBoolSymbol = symbol fBoolId [boolSort] boolSort & function

fStringSymbol :: Symbol
fStringSymbol = symbol fStringId [stringSort] stringSort & function

fTestIntSymbol :: Symbol
fTestIntSymbol = symbol fTestIntId [testSort] intSort & function

fTestFunctionalIntSymbol :: Symbol
fTestFunctionalIntSymbol =
    symbol fTestFunctionalIntId [testSort] intSort & function & functional

plain00Symbol :: Symbol
plain00Symbol = symbol plain00Id [] testSort

plain00Sort0Symbol :: Symbol
plain00Sort0Symbol = symbol plain00Sort0Id [] testSort0

plain00SubsortSymbol :: Symbol
plain00SubsortSymbol = symbol plain00SubsortId [] subSort

plain00OtherSortSymbol :: Symbol
plain00OtherSortSymbol = symbol plain00OtherSortId [] otherSort

plain00SubSubsortSymbol :: Symbol
plain00SubSubsortSymbol = symbol plain00SubSubsortId [] subSubsort

plain10Symbol :: Symbol
plain10Symbol = symbol plain10Id [testSort] testSort

plain11Symbol :: Symbol
plain11Symbol = symbol plain11Id [testSort] testSort

plain20Symbol :: Symbol
plain20Symbol = symbol plain20Id [testSort, testSort] testSort

constr00Symbol :: Symbol
constr00Symbol = symbol constr00Id [] testSort & constructor

constr10Symbol :: Symbol
constr10Symbol = symbol constr10Id [testSort] testSort & constructor

constr11Symbol :: Symbol
constr11Symbol = symbol constr11Id [testSort] testSort & constructor

constr20Symbol :: Symbol
constr20Symbol = symbol constr20Id [testSort, testSort] testSort & constructor

constrFunct20TestMapSymbol :: Symbol
constrFunct20TestMapSymbol =
    symbol constrFunct20TestMapId [testSort, mapSort] testSort
        & constructor
        & function

function20MapTestSymbol :: Symbol
function20MapTestSymbol =
    symbol function20MapTestId [mapSort, testSort] testSort & function

functional00Symbol :: Symbol
functional00Symbol = symbol functional00Id [] testSort & functional

functional01Symbol :: Symbol
functional01Symbol = symbol functional01Id [] testSort & functional

functional10Symbol :: Symbol
functional10Symbol = symbol functional10Id [testSort] testSort & functional

functional11Symbol :: Symbol
functional11Symbol = symbol functional11Id [testSort] testSort & functional

functional20Symbol :: Symbol
functional20Symbol =
    symbol functional20Id [testSort, testSort] testSort & functional

functional00SubSubSortSymbol :: Symbol
functional00SubSubSortSymbol =
    symbol functional00SubSubSortId [] subSubsort & functional

functionalInjective00Symbol :: Symbol
functionalInjective00Symbol =
    symbol functionalInjective00Id [] testSort & functional & injective

functionalConstr10Symbol :: Symbol
functionalConstr10Symbol =
    symbol functionalConstr10Id [testSort] testSort & functional & constructor

functionalConstr11Symbol :: Symbol
functionalConstr11Symbol =
    symbol functionalConstr11Id [testSort] testSort & functional & constructor

functionalConstr12Symbol :: Symbol
functionalConstr12Symbol =
    symbol functionalConstr12Id [testSort] testSort & functional & constructor

functionalConstr20Symbol :: Symbol
functionalConstr20Symbol =
    symbol functionalConstr20Id [testSort, testSort] testSort
        & functional
        & constructor

functionalConstr21Symbol :: Symbol
functionalConstr21Symbol =
    symbol functionalConstr21Id [testSort, testSort] testSort
        & functional
        & constructor

functionalConstr30Symbol :: Symbol
functionalConstr30Symbol =
    symbol functionalConstr30Id [testSort, testSort, testSort] testSort
        & functional
        & constructor

functionalTopConstr20Symbol :: Symbol
functionalTopConstr20Symbol =
    symbol functionalTopConstr20Id [topSort, testSort] testSort
        & functional
        & constructor

functionalTopConstr21Symbol :: Symbol
functionalTopConstr21Symbol =
    symbol functionalTopConstr21Id [testSort, topSort] testSort
        & functional
        & constructor

fMapSymbol :: Symbol
fMapSymbol =
    symbol fMapId [mapSort] testSort & function

injective10Symbol :: Symbol
injective10Symbol = symbol injective10Id [testSort] testSort & injective

injective11Symbol :: Symbol
injective11Symbol = symbol injective11Id [testSort] testSort & injective

sortInjectionSymbol :: Sort -> Sort -> Symbol
sortInjectionSymbol fromSort toSort =
    Symbol
        { symbolConstructor = sortInjectionId
        , symbolParams = [fromSort, toSort]
        , symbolAttributes = Mock.sortInjectionAttributes
        , symbolSorts = applicationSorts [fromSort] toSort
        }

sortInjection10Symbol :: Symbol
sortInjection10Symbol = sortInjectionSymbol testSort0 testSort

sortInjection11Symbol :: Symbol
sortInjection11Symbol = sortInjectionSymbol testSort1 testSort

sortInjection0ToTopSymbol :: Symbol
sortInjection0ToTopSymbol = sortInjectionSymbol testSort0 topSort

sortInjectionSubToTopSymbol :: Symbol
sortInjectionSubToTopSymbol = sortInjectionSymbol subSort topSort

sortInjectionSubSubToTopSymbol :: Symbol
sortInjectionSubSubToTopSymbol = sortInjectionSymbol subSubsort topSort

sortInjectionSubSubToSubSymbol :: Symbol
sortInjectionSubSubToSubSymbol = sortInjectionSymbol subSubsort subSort

sortInjectionSubSubToOtherSymbol :: Symbol
sortInjectionSubSubToOtherSymbol = sortInjectionSymbol subSubsort otherSort

sortInjectionSubOtherToOtherSymbol :: Symbol
sortInjectionSubOtherToOtherSymbol = sortInjectionSymbol subOthersort otherSort

sortInjectionSubOtherToTopSymbol :: Symbol
sortInjectionSubOtherToTopSymbol = sortInjectionSymbol subOthersort topSort

sortInjectionSubToTestSymbol :: Symbol
sortInjectionSubToTestSymbol = sortInjectionSymbol testSort topSort

sortInjectionTestToTopSymbol :: Symbol
sortInjectionTestToTopSymbol = sortInjectionSymbol subSort testSort

sortInjectionOtherToTopSymbol :: Symbol
sortInjectionOtherToTopSymbol = sortInjectionSymbol otherSort topSort

sortInjectionOtherToOverTheTopSymbol :: Symbol
sortInjectionOtherToOverTheTopSymbol =
    sortInjectionSymbol otherSort overTheTopSort

sortInjectionSubToOverTheTopSymbol :: Symbol
sortInjectionSubToOverTheTopSymbol = sortInjectionSymbol subSort overTheTopSort

sortInjectionTopToOverTheTopSymbol :: Symbol
sortInjectionTopToOverTheTopSymbol = sortInjectionSymbol topSort overTheTopSort

sortInjectionOtherToOtherTopSymbol :: Symbol
sortInjectionOtherToOtherTopSymbol = sortInjectionSymbol otherSort otherTopSort

sortInjectionSubToOtherTopSymbol :: Symbol
sortInjectionSubToOtherTopSymbol = sortInjectionSymbol subSort otherTopSort

subsubOverloadSymbol :: Symbol
subsubOverloadSymbol =
    symbol subsubOverloadId [subSubsort] subSubsort & functional & injective

subOverloadSymbol :: Symbol
subOverloadSymbol =
    symbol subOverloadId [subSort] subSort & functional & injective

otherOverloadSymbol :: Symbol
otherOverloadSymbol =
    symbol otherOverloadId [otherSort] otherSort & functional & injective

topOverloadSymbol :: Symbol
topOverloadSymbol =
    symbol topOverloadId [topSort] topSort & functional & injective

unitMapSymbol :: Symbol
unitMapSymbol =
    symbol unitMapId [] mapSort
        & functional
        & hook "MAP.unit"

elementMapSymbol :: Symbol
elementMapSymbol =
    symbol elementMapId [testSort, testSort] mapSort
        & functional
        & hook "MAP.element"

concatMapSymbol :: Symbol
concatMapSymbol =
    symbol concatMapId [mapSort, mapSort] mapSort
        & function
        & hook "MAP.concat"

opaqueMapSymbol :: Symbol
opaqueMapSymbol =
    symbol opaqueMapId [testSort] mapSort
        & function

inKeysMapSymbol :: Symbol
inKeysMapSymbol =
    symbol inKeysMapId [testSort, mapSort] boolSort
        & hook "MAP.in_keys"

lessIntSymbol :: Symbol
lessIntSymbol =
    symbol lessIntId [intSort, intSort] boolSort
        & functional
        & hook "INT.lt"
        & smthook "<"

greaterEqIntSymbol :: Symbol
greaterEqIntSymbol =
    symbol greaterEqIntId [intSort, intSort] boolSort
        & functional
        & hook "INT.ge"
        & smthook ">="

tdivIntSymbol :: Symbol
tdivIntSymbol =
    symbol tdivIntId [intSort, intSort] intSort
        & function
        & hook "INT.tdiv"
        & smthook "div"

concatListSymbol :: Symbol
concatListSymbol =
    symbol concatListId [listSort, listSort] listSort
        & functional
        & hook "LIST.concat"

elementListSymbol :: Symbol
elementListSymbol =
    symbol elementListId [testSort] listSort
        & functional
        & hook "LIST.element"

unitListSymbol :: Symbol
unitListSymbol = symbol unitListId [] listSort & functional & hook "LIST.unit"

concatSetSymbol :: Symbol
concatSetSymbol =
    symbol concatSetId [setSort, setSort] setSort
        & function
        & hook "SET.concat"

elementSetSymbol :: Symbol
elementSetSymbol =
    symbol elementSetId [testSort] setSort & functional & hook "SET.element"

unitSetSymbol :: Symbol
unitSetSymbol =
    symbol unitSetId [] setSort & functional & hook "SET.unit"

keqBoolSymbol :: Symbol
keqBoolSymbol =
    symbol keqBoolId [testSort, testSort] boolSort
        & function
        & functional
        & hook "KEQUAL.eq"

opaqueSetSymbol :: Symbol
opaqueSetSymbol =
    symbol opaqueSetId [testSort] setSort
        & function

sigmaSymbol :: Symbol
sigmaSymbol =
    symbol sigmaId [testSort, testSort] testSort
        & functional
        & constructor

anywhereSymbol :: Symbol
anywhereSymbol =
    symbol anywhereId [] testSort
        & functional
        & Lens.set
            (typed @Attribute.Symbol . typed @Attribute.Anywhere)
            (Attribute.Anywhere True)

functionSMTSymbol :: Symbol
functionSMTSymbol =
    symbol functionSMTId [testSort] testSort & function

functionalSMTSymbol :: Symbol
functionalSMTSymbol =
    symbol functionalSMTId [testSort] testSort & function & functional

type MockElementVariable = ElementVariable VariableName

pattern MockElementVariable ::
    Id -> VariableCounter -> Sort -> MockElementVariable
pattern MockElementVariable base counter variableSort =
    Variable
        { variableName = ElementVariableName VariableName{base, counter}
        , variableSort
        }

type MockRewritingElementVariable = ElementVariable RewritingVariableName

mkRuleElementVariable ::
    Id -> VariableCounter -> Sort -> MockRewritingElementVariable
mkRuleElementVariable base counter variableSort =
    Variable
        { variableName =
            ElementVariableName $
                mkRuleVariable VariableName{base, counter}
        , variableSort
        }
mkConfigElementVariable ::
    Id -> VariableCounter -> Sort -> MockRewritingElementVariable
mkConfigElementVariable base counter variableSort =
    Variable
        { variableName =
            ElementVariableName $
                mkConfigVariable VariableName{base, counter}
        , variableSort
        }
mkEquationElementVariable ::
    Id -> VariableCounter -> Sort -> MockRewritingElementVariable
mkEquationElementVariable base counter variableSort =
    Variable
        { variableName =
            ElementVariableName $
                mkEquationVariable VariableName{base, counter}
        , variableSort
        }

type MockSetVariable = SetVariable VariableName

pattern MockSetVariable ::
    Id -> VariableCounter -> Sort -> MockSetVariable
pattern MockSetVariable base counter variableSort =
    Variable
        { variableName = SetVariableName VariableName{base, counter}
        , variableSort
        }

type MockRewritingSetVariable = SetVariable RewritingVariableName

mkRuleSetVariable ::
    Id -> VariableCounter -> Sort -> MockRewritingSetVariable
mkRuleSetVariable base counter variableSort =
    Variable
        { variableName =
            SetVariableName $
                mkRuleVariable VariableName{base, counter}
        , variableSort
        }

mkConfigSetVariable ::
    Id -> VariableCounter -> Sort -> MockRewritingSetVariable
mkConfigSetVariable base counter variableSort =
    Variable
        { variableName =
            SetVariableName $
                mkConfigVariable VariableName{base, counter}
        , variableSort
        }

var_x_0 :: MockElementVariable
var_x_0 = MockElementVariable (testId "x") (Just (Element 0)) testSort
var_xRule_0 :: MockRewritingElementVariable
var_xRule_0 = mkRuleElementVariable (testId "x") (Just (Element 0)) testSort
var_xConfig_0 :: MockRewritingElementVariable
var_xConfig_0 = mkConfigElementVariable (testId "x") (Just (Element 0)) testSort
var_x_1 :: MockElementVariable
var_x_1 = MockElementVariable (testId "x") (Just (Element 1)) testSort
var_xRule_1 :: MockRewritingElementVariable
var_xRule_1 = mkRuleElementVariable (testId "x") (Just (Element 1)) testSort
var_xConfig_1 :: MockRewritingElementVariable
var_xConfig_1 = mkConfigElementVariable (testId "x") (Just (Element 1)) testSort
var_y_1 :: MockElementVariable
var_y_1 = MockElementVariable (testId "y") (Just (Element 1)) testSort
var_yRule_1 :: MockRewritingElementVariable
var_yRule_1 = mkRuleElementVariable (testId "y") (Just (Element 1)) testSort
var_yConfig_1 :: MockRewritingElementVariable
var_yConfig_1 = mkConfigElementVariable (testId "y") (Just (Element 1)) testSort
var_z_1 :: MockElementVariable
var_z_1 = MockElementVariable (testId "z") (Just (Element 1)) testSort
var_zRule_1 :: MockRewritingElementVariable
var_zRule_1 = mkRuleElementVariable (testId "z") (Just (Element 1)) testSort
var_zConfig_1 :: MockRewritingElementVariable
var_zConfig_1 = mkConfigElementVariable (testId "z") (Just (Element 1)) testSort
x :: MockElementVariable
x = MockElementVariable (testId "x") mempty testSort
xRule :: MockRewritingElementVariable
xRule = mkRuleElementVariable (testId "x") mempty testSort
xConfig :: MockRewritingElementVariable
xConfig = mkConfigElementVariable (testId "x") mempty testSort
setX :: MockSetVariable
setX = MockSetVariable (testId "@x") mempty testSort
setXRule :: MockRewritingSetVariable
setXRule = mkRuleSetVariable (testId "@x") mempty testSort
setXConfig :: MockRewritingSetVariable
setXConfig = mkConfigSetVariable (testId "@x") mempty testSort
var_setX_0 :: MockSetVariable
var_setX_0 = MockSetVariable (testId "@x") (Just (Element 0)) testSort
var_setXConfig_0 :: MockRewritingSetVariable
var_setXConfig_0 =
    mkConfigSetVariable (testId "@x") (Just (Element 0)) testSort
var_setXRule_0 :: MockRewritingSetVariable
var_setXRule_0 =
    mkRuleSetVariable (testId "@x") (Just (Element 0)) testSort
x0 :: MockElementVariable
x0 = MockElementVariable (testId "x0") mempty testSort0
xConfig0 :: MockRewritingElementVariable
xConfig0 = mkConfigElementVariable (testId "x0") mempty testSort0
y :: MockElementVariable
y = MockElementVariable (testId "y") mempty testSort
yRule :: MockRewritingElementVariable
yRule = mkRuleElementVariable (testId "y") mempty testSort
yConfig :: MockRewritingElementVariable
yConfig = mkConfigElementVariable (testId "y") mempty testSort
setY :: MockSetVariable
setY = MockSetVariable (testId "@y") mempty testSort
setYRule :: MockRewritingSetVariable
setYRule = mkRuleSetVariable (testId "@y") mempty testSort
setYConfig :: MockRewritingSetVariable
setYConfig = mkConfigSetVariable (testId "@y") mempty testSort
z :: MockElementVariable
z = MockElementVariable (testId "z") mempty testSort
zRule :: MockRewritingElementVariable
zRule = mkRuleElementVariable (testId "z") mempty testSort
zConfig :: MockRewritingElementVariable
zConfig = mkConfigElementVariable (testId "z") mempty testSort
xEquation :: MockRewritingElementVariable
xEquation = mkEquationElementVariable (testId "x") mempty testSort
yEquation :: MockRewritingElementVariable
yEquation = mkEquationElementVariable (testId "y") mempty setSort
zEquation :: MockRewritingElementVariable
zEquation = mkEquationElementVariable (testId "z") mempty testSort
t :: MockElementVariable
t = MockElementVariable (testId "t") mempty testSort
tRule :: MockRewritingElementVariable
tRule = mkRuleElementVariable (testId "t") mempty testSort
tConfig :: MockRewritingElementVariable
tConfig = mkConfigElementVariable (testId "t") mempty testSort
u :: MockElementVariable
u = MockElementVariable (testId "u") mempty testSort
uRule :: MockRewritingElementVariable
uRule = mkRuleElementVariable (testId "u") mempty testSort
uConfig :: MockRewritingElementVariable
uConfig = mkConfigElementVariable (testId "u") mempty testSort
m :: MockElementVariable
m = MockElementVariable (testId "m") mempty mapSort
mRule :: MockRewritingElementVariable
mRule = mkRuleElementVariable (testId "m") mempty mapSort
mConfig :: MockRewritingElementVariable
mConfig = mkConfigElementVariable (testId "m") mempty mapSort
xSet :: MockElementVariable
xSet = MockElementVariable (testId "xSet") mempty setSort
xRuleSet :: MockRewritingElementVariable
xRuleSet = mkRuleElementVariable (testId "xSet") mempty setSort
xConfigSet :: MockRewritingElementVariable
xConfigSet = mkConfigElementVariable (testId "xSet") mempty setSort
ySet :: MockElementVariable
ySet = MockElementVariable (testId "ySet") mempty setSort
xInt :: MockElementVariable
xInt = MockElementVariable (testId "xInt") mempty intSort
xRuleInt :: MockRewritingElementVariable
xRuleInt = mkRuleElementVariable (testId "xInt") mempty intSort
xConfigInt :: MockRewritingElementVariable
xConfigInt = mkConfigElementVariable (testId "xInt") mempty intSort
yInt :: MockElementVariable
yInt = MockElementVariable (testId "yInt") mempty intSort
xBool :: MockElementVariable
xBool = MockElementVariable (testId "xBool") mempty boolSort
xRuleBool :: MockRewritingElementVariable
xRuleBool = mkRuleElementVariable (testId "xBool") mempty boolSort
xConfigBool :: MockRewritingElementVariable
xConfigBool = mkConfigElementVariable (testId "xBool") mempty boolSort
xString :: MockElementVariable
xString = MockElementVariable (testId "xString") mempty stringSort
xRuleString :: MockRewritingElementVariable
xRuleString = mkRuleElementVariable (testId "xString") mempty stringSort
xConfigString :: MockRewritingElementVariable
xConfigString = mkConfigElementVariable (testId "xString") mempty stringSort
xList :: MockElementVariable
xList = MockElementVariable (testId "xList") mempty listSort
xConfigList :: MockRewritingElementVariable
xConfigList = mkConfigElementVariable (testId "xList") mempty listSort
xMap :: MockElementVariable
xMap = MockElementVariable (testId "xMap") mempty mapSort
yMap :: MockElementVariable
yMap = MockElementVariable (testId "yMap") mempty mapSort
zMap :: MockElementVariable
zMap = MockElementVariable (testId "zMap") mempty mapSort
xMapRule :: MockRewritingElementVariable
xMapRule = mkRuleElementVariable (testId "xMap") mempty mapSort
xMapConfig :: MockRewritingElementVariable
xMapConfig = mkConfigElementVariable (testId "xMap") mempty mapSort
yMapRule :: MockRewritingElementVariable
yMapRule = mkRuleElementVariable (testId "yMap") mempty mapSort
yMapConfig :: MockRewritingElementVariable
yMapConfig = mkConfigElementVariable (testId "yMap") mempty mapSort
zMapRule :: MockRewritingElementVariable
zMapRule = mkRuleElementVariable (testId "zMap") mempty mapSort
zMapConfig :: MockRewritingElementVariable
zMapConfig = mkConfigElementVariable (testId "zMap") mempty mapSort
xSubSort :: MockElementVariable
xSubSort = MockElementVariable (testId "xSubSort") mempty subSort
xRuleSubSort :: MockRewritingElementVariable
xRuleSubSort = mkRuleElementVariable (testId "xSubSort") mempty subSort
xConfigSubSort :: MockRewritingElementVariable
xConfigSubSort = mkConfigElementVariable (testId "xSubSort") mempty subSort
xSubSubSort :: MockElementVariable
xSubSubSort =
    MockElementVariable (testId "xSubSubSort") mempty subSubsort
xConfigSubSubSort :: MockRewritingElementVariable
xConfigSubSubSort =
    mkConfigElementVariable (testId "xSubSubSort") mempty subSubsort
xSubOtherSort :: MockElementVariable
xSubOtherSort =
    MockElementVariable (testId "xSubOtherSort") mempty subOthersort
xRuleSubOtherSort :: MockRewritingElementVariable
xRuleSubOtherSort =
    mkRuleElementVariable (testId "xSubOtherSort") mempty subOthersort
xConfigSubOtherSort :: MockRewritingElementVariable
xConfigSubOtherSort =
    mkConfigElementVariable (testId "xSubOtherSort") mempty subOthersort
xOtherSort :: MockElementVariable
xOtherSort = MockElementVariable (testId "xOtherSort") mempty otherSort
xConfigOtherSort :: MockRewritingElementVariable
xConfigOtherSort = mkConfigElementVariable (testId "xOtherSort") mempty otherSort
xTopSort :: MockElementVariable
xTopSort = MockElementVariable (testId "xTopSort") mempty topSort
xConfigTopSort :: MockRewritingElementVariable
xConfigTopSort = mkConfigElementVariable (testId "xTopSort") mempty topSort
xStringMetaSort :: MockSetVariable
xStringMetaSort = MockSetVariable (testId "xStringMetaSort") mempty stringMetaSort
xRuleStringMetaSort :: MockRewritingSetVariable
xRuleStringMetaSort =
    mkRuleSetVariable (testId "xStringMetaSort") mempty stringMetaSort
xConfigStringMetaSort :: MockRewritingSetVariable
xConfigStringMetaSort =
    mkConfigSetVariable (testId "xStringMetaSort") mempty stringMetaSort

makeSomeVariable :: Text -> Sort -> SomeVariable VariableName
makeSomeVariable name variableSort =
    Variable
        { variableSort
        , variableName
        }
  where
    variableName =
        injectVariableName VariableName{base = testId name, counter = mempty}
    injectVariableName
        | Text.head name == '@' = inject . SetVariableName
        | otherwise = inject . ElementVariableName

makeSomeConfigVariable :: Text -> Sort -> SomeVariable RewritingVariableName
makeSomeConfigVariable name variableSort =
    Variable
        { variableSort
        , variableName
        }
  where
    variableName =
        injectVariableName $
            mkConfigVariable VariableName{base = testId name, counter = mempty}
    injectVariableName
        | Text.head name == '@' = inject . SetVariableName
        | otherwise = inject . ElementVariableName

makeTestSomeVariable :: Text -> SomeVariable VariableName
makeTestSomeVariable = (`makeSomeVariable` testSort)

makeTestSomeConfigVariable :: Text -> SomeVariable RewritingVariableName
makeTestSomeConfigVariable = (`makeSomeConfigVariable` testSort)

mkTestSomeVariable :: Text -> TermLike VariableName
mkTestSomeVariable = Internal.mkVar . makeTestSomeVariable

mkTestSomeConfigVariable :: Text -> TermLike RewritingVariableName
mkTestSomeConfigVariable = Internal.mkVar . makeTestSomeConfigVariable

a :: InternalVariable variable => TermLike variable
a = Internal.mkApplySymbol aSymbol []

aConcrete :: TermLike Concrete
Just aConcrete = Internal.asConcrete (a :: TermLike VariableName)

aSort0 :: InternalVariable variable => TermLike variable
aSort0 = Internal.mkApplySymbol aSort0Symbol []

aSort1 :: InternalVariable variable => TermLike variable
aSort1 = Internal.mkApplySymbol aSort1Symbol []

aSubsort :: InternalVariable variable => TermLike variable
aSubsort = Internal.mkApplySymbol aSubsortSymbol []

aSubOthersort :: InternalVariable variable => TermLike variable
aSubOthersort = Internal.mkApplySymbol aSubOthersortSymbol []

aSubSubsort :: InternalVariable variable => TermLike variable
aSubSubsort = Internal.mkApplySymbol aSubSubsortSymbol []

aTopSort :: InternalVariable variable => TermLike variable
aTopSort = Internal.mkApplySymbol aTopSortSymbol []

aOtherSort :: InternalVariable variable => TermLike variable
aOtherSort = Internal.mkApplySymbol aOtherSortSymbol []

b :: InternalVariable variable => TermLike variable
b = Internal.mkApplySymbol bSymbol []

bConcrete :: TermLike Concrete
Just bConcrete = Internal.asConcrete (b :: TermLike VariableName)

bSort0 :: InternalVariable variable => TermLike variable
bSort0 = Internal.mkApplySymbol bSort0Symbol []

c :: InternalVariable variable => TermLike variable
c = Internal.mkApplySymbol cSymbol []

d :: InternalVariable variable => TermLike variable
d = Internal.mkApplySymbol dSymbol []

e :: InternalVariable variable => TermLike variable
e = Internal.mkApplySymbol eSymbol []

f
    , g
    , h ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable ->
        TermLike variable
f arg = Internal.mkApplySymbol fSymbol [arg]
g arg = Internal.mkApplySymbol gSymbol [arg]
h arg = Internal.mkApplySymbol hSymbol [arg]

fSort0
    , gSort0 ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable ->
        TermLike variable
fSort0 arg = Internal.mkApplySymbol fSort0Symbol [arg]
gSort0 arg = Internal.mkApplySymbol gSort0Symbol [arg]

cf :: InternalVariable variable => TermLike variable
cf = Internal.mkApplySymbol cfSymbol []

cfSort0 :: InternalVariable variable => TermLike variable
cfSort0 = Internal.mkApplySymbol cfSort0Symbol []

cfSort1 :: InternalVariable variable => TermLike variable
cfSort1 = Internal.mkApplySymbol cfSort1Symbol []

cg :: InternalVariable variable => TermLike variable
cg = Internal.mkApplySymbol cgSymbol []

cgSort0 :: InternalVariable variable => TermLike variable
cgSort0 = Internal.mkApplySymbol cgSort0Symbol []

ch :: InternalVariable variable => TermLike variable
ch = Internal.mkApplySymbol chSymbol []

fSet ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
fSet arg = Internal.mkApplySymbol fSetSymbol [arg]

fTestInt ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
fTestInt arg = Internal.mkApplySymbol fTestIntSymbol [arg]

fTestFunctionalInt ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
fTestFunctionalInt arg =
    Internal.mkApplySymbol fTestFunctionalIntSymbol [arg]

fInt ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
fInt arg = Internal.mkApplySymbol fIntSymbol [arg]

fBool ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
fBool arg = Internal.mkApplySymbol fBoolSymbol [arg]

fString ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
fString arg = Internal.mkApplySymbol fStringSymbol [arg]

plain00 :: InternalVariable variable => TermLike variable
plain00 = Internal.mkApplySymbol plain00Symbol []

plain00Sort0 :: InternalVariable variable => TermLike variable
plain00Sort0 = Internal.mkApplySymbol plain00Sort0Symbol []

plain00Subsort :: InternalVariable variable => TermLike variable
plain00Subsort = Internal.mkApplySymbol plain00SubsortSymbol []

plain00OtherSort :: InternalVariable variable => TermLike variable
plain00OtherSort = Internal.mkApplySymbol plain00OtherSortSymbol []

plain00SubSubsort :: InternalVariable variable => TermLike variable
plain00SubSubsort = Internal.mkApplySymbol plain00SubSubsortSymbol []

plain10
    , plain11 ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable ->
        TermLike variable
plain10 arg = Internal.mkApplySymbol plain10Symbol [arg]
plain11 arg = Internal.mkApplySymbol plain11Symbol [arg]

plain20 ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
plain20 arg1 arg2 = Internal.mkApplySymbol plain20Symbol [arg1, arg2]

constr00 :: InternalVariable variable => HasCallStack => TermLike variable
constr00 = Internal.mkApplySymbol constr00Symbol []

constr10
    , constr11 ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable ->
        TermLike variable
constr10 arg = Internal.mkApplySymbol constr10Symbol [arg]
constr11 arg = Internal.mkApplySymbol constr11Symbol [arg]

constr20 ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
constr20 arg1 arg2 = Internal.mkApplySymbol constr20Symbol [arg1, arg2]

constrFunct20TestMap ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
constrFunct20TestMap arg1 arg2 =
    Internal.mkApplySymbol constrFunct20TestMapSymbol [arg1, arg2]

function20MapTest ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
function20MapTest arg1 arg2 =
    Internal.mkApplySymbol function20MapTestSymbol [arg1, arg2]

functional00 :: InternalVariable variable => TermLike variable
functional00 = Internal.mkApplySymbol functional00Symbol []

functional01 :: InternalVariable variable => TermLike variable
functional01 = Internal.mkApplySymbol functional01Symbol []

functional10 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
functional10 arg = Internal.mkApplySymbol functional10Symbol [arg]

functional11 ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
functional11 arg = Internal.mkApplySymbol functional11Symbol [arg]

functional20 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
functional20 arg1 arg2 = Internal.mkApplySymbol functional20Symbol [arg1, arg2]

functional00SubSubSort :: InternalVariable variable => TermLike variable
functional00SubSubSort =
    Internal.mkApplySymbol functional00SubSubSortSymbol []

functionalInjective00 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable
functionalInjective00 =
    Internal.mkApplySymbol functionalInjective00Symbol []

functionalConstr10 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
functionalConstr10 arg =
    Internal.mkApplySymbol functionalConstr10Symbol [arg]

functionalConstr11 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
functionalConstr11 arg = Internal.mkApplySymbol functionalConstr11Symbol [arg]

functionalConstr12 ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
functionalConstr12 arg = Internal.mkApplySymbol functionalConstr12Symbol [arg]

functionalConstr20 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
functionalConstr20 arg1 arg2 =
    Internal.mkApplySymbol functionalConstr20Symbol [arg1, arg2]

functionalConstr21 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
functionalConstr21 arg1 arg2 =
    Internal.mkApplySymbol functionalConstr21Symbol [arg1, arg2]

functionalConstr30 ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable ->
    TermLike variable
functionalConstr30 arg1 arg2 arg3 =
    Internal.mkApplySymbol functionalConstr30Symbol [arg1, arg2, arg3]

functionalTopConstr20 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
functionalTopConstr20 arg1 arg2 =
    Internal.mkApplySymbol functionalTopConstr20Symbol [arg1, arg2]

functionalTopConstr21 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
functionalTopConstr21 arg1 arg2 =
    Internal.mkApplySymbol functionalTopConstr21Symbol [arg1, arg2]

subsubOverload ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
subsubOverload arg1 =
    Internal.mkApplySymbol subsubOverloadSymbol [arg1]

subOverload ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
subOverload arg1 =
    Internal.mkApplySymbol subOverloadSymbol [arg1]

otherOverload ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
otherOverload arg1 =
    Internal.mkApplySymbol otherOverloadSymbol [arg1]

topOverload ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
topOverload arg1 =
    Internal.mkApplySymbol topOverloadSymbol [arg1]

injective10 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
injective10 arg = Internal.mkApplySymbol injective10Symbol [arg]

injective11 ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
injective11 arg = Internal.mkApplySymbol injective11Symbol [arg]

sortInjection ::
    InternalVariable variable =>
    Sort ->
    TermLike variable ->
    TermLike variable
sortInjection injTo termLike =
    (synthesize . Internal.InjF)
        Internal.Inj
            { injConstructor
            , injFrom
            , injTo
            , injChild = termLike
            , injAttributes
            }
  where
    injFrom = Internal.termLikeSort termLike
    Symbol{symbolConstructor = injConstructor} = symbol'
    Symbol{symbolAttributes = injAttributes} = symbol'
    symbol' = sortInjectionSymbol injFrom injTo

sortInjection10 ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjection10 = sortInjection testSort

sortInjection11 ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjection11 = sortInjection testSort

sortInjection0ToTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjection0ToTop = sortInjection topSort

sortInjectionSubToTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubToTop = sortInjection topSort

sortInjectionSubSubToTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubSubToTop = sortInjection topSort

sortInjectionSubSubToSub ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubSubToSub = sortInjection subSort

sortInjectionSubSubToOther ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubSubToOther = sortInjection otherSort

sortInjectionSubOtherToOther ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubOtherToOther = sortInjection otherSort

sortInjectionSubOtherToTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubOtherToTop = sortInjection topSort

sortInjectionOtherToOverTheTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionOtherToOverTheTop = sortInjection overTheTopSort

sortInjectionSubToOverTheTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubToOverTheTop = sortInjection overTheTopSort

sortInjectionTopToOverTheTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionTopToOverTheTop = sortInjection overTheTopSort

sortInjectionSubToTest ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubToTest = sortInjection testSort

sortInjectionTestToTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionTestToTop = sortInjection topSort

sortInjectionOtherToTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionOtherToTop = sortInjection topSort

sortInjectionOtherToOtherTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionOtherToOtherTop = sortInjection otherTopSort

sortInjectionSubToOtherTop ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable
sortInjectionSubToOtherTop = sortInjection otherTopSort

unitMap :: InternalVariable variable => TermLike variable
unitMap = Internal.mkApplySymbol unitMapSymbol []

elementMap ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
elementMap m1 m2 = Internal.mkApplySymbol elementMapSymbol [m1, m2]

concatMap ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
concatMap m1 m2 = Internal.mkApplySymbol concatMapSymbol [m1, m2]

opaqueMap ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
opaqueMap term = Internal.mkApplySymbol opaqueMapSymbol [term]

inKeysMap ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
inKeysMap element m1 = Internal.mkApplySymbol inKeysMapSymbol [element, m1]

unitSet :: InternalVariable variable => TermLike variable
unitSet = Internal.mkApplySymbol unitSetSymbol []

elementSet ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
elementSet s1 = Internal.mkApplySymbol elementSetSymbol [s1]

concatSet ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
concatSet s1 s2 = Internal.mkApplySymbol concatSetSymbol [s1, s2]

opaqueSet ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
opaqueSet term = Internal.mkApplySymbol opaqueSetSymbol [term]

lessInt ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
lessInt i1 i2 = Internal.mkApplySymbol lessIntSymbol [i1, i2]

greaterEqInt ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
greaterEqInt i1 i2 = Internal.mkApplySymbol greaterEqIntSymbol [i1, i2]

tdivInt ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
tdivInt i1 i2 = Internal.mkApplySymbol tdivIntSymbol [i1, i2]

concatList ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
concatList l1 l2 = Internal.mkApplySymbol concatListSymbol [l1, l2]

elementList ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable
elementList element = Internal.mkApplySymbol elementListSymbol [element]

unitList ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable
unitList = Internal.mkApplySymbol unitListSymbol []

keqBool ::
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
keqBool t1 t2 = Internal.mkApplySymbol keqBoolSymbol [t1, t2]

sigma ::
    InternalVariable variable =>
    HasCallStack =>
    TermLike variable ->
    TermLike variable ->
    TermLike variable
sigma child1 child2 = Internal.mkApplySymbol sigmaSymbol [child1, child2]

anywhere :: InternalVariable variable => TermLike variable
anywhere = Internal.mkApplySymbol anywhereSymbol []

functionSMT
    , functionalSMT ::
        InternalVariable variable =>
        HasCallStack =>
        TermLike variable ->
        TermLike variable
functionSMT arg =
    Internal.mkApplySymbol functionSMTSymbol [arg]
functionalSMT arg =
    Internal.mkApplySymbol functionalSMTSymbol [arg]

attributesMapping :: [(SymbolOrAlias, Attribute.Symbol)]
attributesMapping =
    map (liftA2 (,) toSymbolOrAlias symbolAttributes) symbols

symbols :: [Symbol]
symbols =
    [ aSymbol
    , aSort0Symbol
    , aSort1Symbol
    , aSubsortSymbol
    , aSubOthersortSymbol
    , aSubSubsortSymbol
    , aTopSortSymbol
    , aOtherSortSymbol
    , bSymbol
    , bSort0Symbol
    , cSymbol
    , dSymbol
    , eSymbol
    , fSymbol
    , fSort0Symbol
    , gSymbol
    , gSort0Symbol
    , hSymbol
    , cfSymbol
    , cfSort0Symbol
    , cfSort1Symbol
    , cgSymbol
    , cgSort0Symbol
    , chSymbol
    , fSetSymbol
    , fIntSymbol
    , fTestIntSymbol
    , plain00Symbol
    , plain00Sort0Symbol
    , plain00SubsortSymbol
    , plain00SubSubsortSymbol
    , plain00OtherSortSymbol
    , plain10Symbol
    , plain11Symbol
    , plain20Symbol
    , constr00Symbol
    , constr10Symbol
    , constr11Symbol
    , constr20Symbol
    , constrFunct20TestMapSymbol
    , function20MapTestSymbol
    , functional00Symbol
    , functional01Symbol
    , functional10Symbol
    , functional11Symbol
    , functional20Symbol
    , functional00SubSubSortSymbol
    , functionalInjective00Symbol
    , functionalConstr10Symbol
    , functionalConstr11Symbol
    , functionalConstr12Symbol
    , functionalConstr20Symbol
    , functionalConstr21Symbol
    , functionalConstr30Symbol
    , functionalTopConstr20Symbol
    , functionalTopConstr21Symbol
    , injective10Symbol
    , injective11Symbol
    , sortInjection10Symbol
    , sortInjection11Symbol
    , sortInjection0ToTopSymbol
    , sortInjectionSubToTopSymbol
    , sortInjectionSubSubToTopSymbol
    , sortInjectionSubSubToSubSymbol
    , sortInjectionSubSubToOtherSymbol
    , sortInjectionSubOtherToOtherSymbol
    , sortInjectionSubOtherToTopSymbol
    , sortInjectionSubToTestSymbol
    , sortInjectionTestToTopSymbol
    , sortInjectionOtherToTopSymbol
    , sortInjectionOtherToOverTheTopSymbol
    , sortInjectionSubToOverTheTopSymbol
    , sortInjectionTopToOverTheTopSymbol
    , sortInjectionSubToOtherTopSymbol
    , sortInjectionOtherToOtherTopSymbol
    , unitMapSymbol
    , elementMapSymbol
    , concatMapSymbol
    , opaqueMapSymbol
    , concatListSymbol
    , elementListSymbol
    , unitListSymbol
    , concatSetSymbol
    , elementSetSymbol
    , unitSetSymbol
    , opaqueSetSymbol
    , lessIntSymbol
    , greaterEqIntSymbol
    , tdivIntSymbol
    , keqBoolSymbol
    , sigmaSymbol
    , anywhereSymbol
    , subsubOverloadSymbol
    , subOverloadSymbol
    , otherOverloadSymbol
    , topOverloadSymbol
    , functionSMTSymbol
    , functionalSMTSymbol
    ]

sortAttributesMapping :: [(Sort, Attribute.Sort)]
sortAttributesMapping =
    [
        ( testSort
        , Default.def
        )
    ,
        ( testSort0
        , Default.def
        )
    ,
        ( testSort1
        , Default.def
        )
    ,
        ( topSort
        , Default.def
        )
    ,
        ( subSort
        , Default.def
        )
    ,
        ( subOthersort
        , Default.def
        )
    ,
        ( subSubsort
        , Default.def
        )
    ,
        ( otherSort
        , Default.def
        )
    ,
        ( otherTopSort
        , Default.def
        )
    ,
        ( mapSort
        , Default.def
            { Attribute.hook = Hook (Just "MAP.Map")
            , Attribute.unit =
                Attribute.Unit (Just $ toSymbolOrAlias unitMapSymbol)
            , Attribute.element =
                Attribute.Element (Just $ toSymbolOrAlias elementMapSymbol)
            , Attribute.concat =
                Attribute.Concat (Just $ toSymbolOrAlias concatMapSymbol)
            }
        )
    ,
        ( listSort
        , Default.def
            { Attribute.hook = Hook (Just "LIST.List")
            , Attribute.unit =
                Attribute.Unit (Just $ toSymbolOrAlias unitListSymbol)
            , Attribute.element =
                Attribute.Element (Just $ toSymbolOrAlias elementListSymbol)
            , Attribute.concat =
                Attribute.Concat (Just $ toSymbolOrAlias concatListSymbol)
            }
        )
    ,
        ( setSort
        , Default.def
            { Attribute.hook = Hook (Just "SET.Set")
            , Attribute.unit =
                Attribute.Unit (Just $ toSymbolOrAlias unitSetSymbol)
            , Attribute.element =
                Attribute.Element (Just $ toSymbolOrAlias elementSetSymbol)
            , Attribute.concat =
                Attribute.Concat (Just $ toSymbolOrAlias concatSetSymbol)
            }
        )
    ,
        ( intSort
        , Default.def{Attribute.hook = Hook (Just "INT.Int")}
        )
    ,
        ( boolSort
        , Default.def{Attribute.hook = Hook (Just "BOOL.Bool")}
        )
    ,
        ( stringSort
        , Default.def{Attribute.hook = Hook (Just "STRING.String")}
        )
    , -- Also add attributes for the implicitly defined sorts.

        ( stringMetaSort
        , Default.def{Attribute.hook = Hook (Just "STRING.String")}
        )
    ]

headSortsMapping :: [(SymbolOrAlias, ApplicationSorts)]
headSortsMapping =
    map ((,) <$> toSymbolOrAlias <*> symbolSorts) symbols

zeroarySmtSort :: Id -> SMT.UnresolvedSort
zeroarySmtSort sortId =
    SMT.Sort
        { smtFromSortArgs = const (const (Just encodedId))
        , declaration =
            SMT.SortDeclarationSort
                SMT.SortDeclaration
                    { name = SMT.encodable sortId
                    , arity = 0
                    }
        }
  where
    encodedId = SMT.encode (SMT.encodable sortId)

builtinZeroarySmtSort :: SMT.SExpr -> SMT.UnresolvedSort
builtinZeroarySmtSort sExpr =
    SMT.Sort
        { smtFromSortArgs = const (const (Just sExpr))
        , declaration = SMT.SortDeclaredIndirectly (SMT.AlreadyEncoded sExpr)
        }

smtBuiltinSymbol ::
    Text -> [Sort] -> Sort -> SMT.UnresolvedSymbol
smtBuiltinSymbol builtin argumentSorts resultSort =
    SMT.Symbol
        { smtFromSortArgs = const (const (Just (SMT.Atom builtin)))
        , declaration =
            SMT.SymbolBuiltin
                SMT.IndirectSymbolDeclaration
                    { name = SMT.AlreadyEncoded $ SMT.Atom builtin
                    , sortDependencies =
                        SMT.SortReference <$> resultSort : argumentSorts
                    }
        }

smtDeclaredSymbol ::
    Text -> Id -> [Sort] -> Sort -> SMT.UnresolvedSymbol
smtDeclaredSymbol smtName id' argumentSorts resultSort =
    SMT.Symbol
        { smtFromSortArgs = const (const (Just (SMT.Atom smtName)))
        , declaration =
            SMT.SymbolDeclaredDirectly
                SMT.FunctionDeclaration
                    { name = SMT.encodable id'
                    , inputSorts = SMT.SortReference <$> argumentSorts
                    , resultSort = SMT.SortReference resultSort
                    }
        }

emptySmtDeclarations :: SMT.SmtDeclarations
emptySmtDeclarations =
    SMT.Declarations
        { sorts = Map.empty
        , symbols = Map.empty
        }

smtDeclarations :: SMT.SmtDeclarations
smtDeclarations = SMT.resolve smtUnresolvedDeclarations

smtUnresolvedDeclarations :: SMT.UnresolvedDeclarations
smtUnresolvedDeclarations =
    SMT.Declarations
        { sorts =
            Map.fromList
                [ (testSort0Id, zeroarySmtSort testSort0Id)
                , (testSort1Id, zeroarySmtSort testSort1Id)
                , (topSortId, zeroarySmtSort topSortId)
                , (topSortId, zeroarySmtSort subSortId)
                , (topSortId, zeroarySmtSort subSubsortId)
                , (topSortId, zeroarySmtSort otherSortId)
                , -- TODO(virgil): testSort has constructors, it should have a
                  -- constructor-based definition. The same for others.
                  (testSortId, zeroarySmtSort testSortId)
                , (intSortId, builtinZeroarySmtSort SMT.tInt)
                , (boolSortId, builtinZeroarySmtSort SMT.tBool)
                ]
        , symbols =
            Map.fromList
                [ (lessIntId, smtBuiltinSymbol "<" [intSort, intSort] boolSort)
                , (greaterEqIntId, smtBuiltinSymbol ">=" [intSort, intSort] boolSort)
                , (tdivIntId, smtBuiltinSymbol "div" [intSort, intSort] intSort)
                ,
                    ( functional00Id
                    , smtDeclaredSymbol "functional00" functional00Id [] testSort
                    )
                ,
                    ( functionSMTId
                    , smtDeclaredSymbol "functionSMT" functionSMTId [testSort] testSort
                    )
                ,
                    ( functionalSMTId
                    , smtDeclaredSymbol "functionalSMT" functionalSMTId [testSort] testSort
                    )
                ]
        }

sortConstructors :: Map.Map Id Attribute.Constructors
sortConstructors =
    -- TODO(virgil): testSort has constructors, it should have a
    -- constructor-based definition. The same for others.
    Map.empty

testSortId :: Id
testSortId = testId "testSort"
testSort0Id :: Id
testSort0Id = testId "testSort0"
testSort1Id :: Id
testSort1Id = testId "testSort1"
topSortId :: Id
topSortId = testId "topSort"
overTheTopSortId :: Id
overTheTopSortId = testId "overTheTopSort"
subSortId :: Id
subSortId = testId "subSort"
subOthersortId :: Id
subOthersortId = testId "subOthersort"
subSubsortId :: Id
subSubsortId = testId "subSubsort"
otherSortId :: Id
otherSortId = testId "otherSort"
otherTopSortId :: Id
otherTopSortId = testId "otherTopSort"
intSortId :: Id
intSortId = testId "intSort"
boolSortId :: Id
boolSortId = testId "boolSort"
stringSortId :: Id
stringSortId = testId "stringSort"

testSort :: Sort
testSort =
    SortActualSort
        SortActual
            { sortActualName = testSortId
            , sortActualSorts = []
            }

testSort0 :: Sort
testSort0 =
    SortActualSort
        SortActual
            { sortActualName = testSort0Id
            , sortActualSorts = []
            }

testSort1 :: Sort
testSort1 =
    SortActualSort
        SortActual
            { sortActualName = testSort1Id
            , sortActualSorts = []
            }

topSort :: Sort
topSort =
    SortActualSort
        SortActual
            { sortActualName = topSortId
            , sortActualSorts = []
            }

overTheTopSort :: Sort
overTheTopSort =
    SortActualSort
        SortActual
            { sortActualName = overTheTopSortId
            , sortActualSorts = []
            }

subSort :: Sort
subSort =
    SortActualSort
        SortActual
            { sortActualName = subSortId
            , sortActualSorts = []
            }

subOthersort :: Sort
subOthersort =
    SortActualSort
        SortActual
            { sortActualName = subOthersortId
            , sortActualSorts = []
            }

subSubsort :: Sort
subSubsort =
    SortActualSort
        SortActual
            { sortActualName = subSubsortId
            , sortActualSorts = []
            }

otherSort :: Sort
otherSort =
    SortActualSort
        SortActual
            { sortActualName = otherSortId
            , sortActualSorts = []
            }

otherTopSort :: Sort
otherTopSort =
    SortActualSort
        SortActual
            { sortActualName = otherTopSortId
            , sortActualSorts = []
            }

mapSort :: Sort
mapSort =
    SortActualSort
        SortActual
            { sortActualName = testId "mapSort"
            , sortActualSorts = []
            }

setSort :: Sort
setSort =
    SortActualSort
        SortActual
            { sortActualName = testId "setSort"
            , sortActualSorts = []
            }

listSort :: Sort
listSort =
    SortActualSort
        SortActual
            { sortActualName = testId "listSort"
            , sortActualSorts = []
            }

intSort :: Sort
intSort =
    SortActualSort
        SortActual
            { sortActualName = intSortId
            , sortActualSorts = []
            }

stringSort :: Sort
stringSort =
    SortActualSort
        SortActual
            { sortActualName = stringSortId
            , sortActualSorts = []
            }

boolSort :: Sort
boolSort =
    SortActualSort
        SortActual
            { sortActualName = boolSortId
            , sortActualSorts = []
            }

subsorts :: [(Sort, Sort)]
subsorts =
    [ (subSubsort, subSort)
    , (subSubsort, topSort)
    , (subSort, topSort)
    , (testSort, topSort)
    , (subSubsort, otherSort)
    , (subOthersort, otherSort)
    , (otherSort, topSort)
    , (otherSort, otherTopSort)
    , (subSort, otherTopSort)
    , (subSort, testSort)
    , (testSort0, testSort)
    , (mapSort, testSort)
    , (listSort, testSort)
    , (topSort, overTheTopSort)
    ]

overloads :: [(Symbol, Symbol)]
overloads =
    [ (subOverloadSymbol, subsubOverloadSymbol)
    , (otherOverloadSymbol, subsubOverloadSymbol)
    , (topOverloadSymbol, subsubOverloadSymbol)
    , (topOverloadSymbol, subOverloadSymbol)
    , (topOverloadSymbol, otherOverloadSymbol)
    ]

builtinMap ::
    InternalVariable variable =>
    [(TermLike variable, TermLike variable)] ->
    TermLike variable
builtinMap elements = framedMap elements []

test_builtinMap :: [TestTree]
test_builtinMap =
    [ testCase "constructor-like keys" $ do
        let input = builtinMap [(a, a), (b, b)] :: TermLike VariableName
        assertBool "" (isConstructorLike input)
    , testCase "symbolic keys" $ do
        let input = builtinMap [(f a, a), (f b, b)] :: TermLike VariableName
        assertBool "" (not $ isConstructorLike input)
    ]

framedMap ::
    InternalVariable variable =>
    [(TermLike variable, TermLike variable)] ->
    [TermLike variable] ->
    TermLike variable
framedMap elements opaque =
    framedInternalMap elements opaque & Internal.mkInternalMap

framedInternalMap ::
    [(TermLike variable, TermLike variable)] ->
    [TermLike variable] ->
    InternalMap Internal.Key (TermLike variable)
framedInternalMap elements opaque =
    InternalAc
        { builtinAcSort = mapSort
        , builtinAcUnit = unitMapSymbol
        , builtinAcElement = elementMapSymbol
        , builtinAcConcat = concatMapSymbol
        , builtinAcChild =
            NormalizedMap
                NormalizedAc
                    { elementsWithVariables = wrapElement <$> abstractElements
                    , concreteElements
                    , opaque
                    }
        }
  where
    asConcrete element@(key, value) =
        (,) <$> retractKey key <*> pure value
            & maybe (Left element) Right
    (abstractElements, HashMap.fromList -> concreteElements) =
        asConcrete . Bifunctor.second MapValue <$> elements
            & partitionEithers

builtinList ::
    InternalVariable variable =>
    [TermLike variable] ->
    TermLike variable
builtinList child =
    Internal.mkInternalList
        InternalList
            { internalListSort = listSort
            , internalListUnit = unitListSymbol
            , internalListElement = elementListSymbol
            , internalListConcat = concatListSymbol
            , internalListChild = Seq.fromList child
            }

builtinSet ::
    InternalVariable variable =>
    [TermLike variable] ->
    TermLike variable
builtinSet elements = framedSet elements []

test_builtinSet :: [TestTree]
test_builtinSet =
    [ testCase "constructor-like keys" $ do
        let input = builtinSet [a, b] :: TermLike VariableName
        assertBool "" (isConstructorLike input)
    , testCase "symbolic keys" $ do
        let input = builtinSet [f a, f b] :: TermLike VariableName
        assertBool "" (not $ isConstructorLike input)
    ]

framedSet ::
    InternalVariable variable =>
    [TermLike variable] ->
    [TermLike variable] ->
    TermLike variable
framedSet elements opaque =
    framedInternalSet elements opaque & Internal.mkInternalSet

framedInternalSet ::
    [TermLike variable] ->
    [TermLike variable] ->
    InternalSet Internal.Key (TermLike variable)
framedInternalSet elements opaque =
    InternalAc
        { builtinAcSort = setSort
        , builtinAcUnit = unitSetSymbol
        , builtinAcElement = elementSetSymbol
        , builtinAcConcat = concatSetSymbol
        , builtinAcChild =
            NormalizedSet
                NormalizedAc
                    { elementsWithVariables = wrapElement <$> abstractElements
                    , concreteElements
                    , opaque
                    }
        }
  where
    asConcrete key =
        do
            Monad.guard (isConstructorLike key)
            (,) <$> retractKey key <*> pure SetValue
            & maybe (Left (key, SetValue)) Right
    (abstractElements, HashMap.fromList -> concreteElements) =
        asConcrete <$> elements
            & partitionEithers

builtinInt ::
    InternalVariable variable =>
    Integer ->
    TermLike variable
builtinInt = Builtin.Int.asInternal intSort

builtinBool ::
    InternalVariable variable =>
    Bool ->
    TermLike variable
builtinBool = Builtin.Bool.asInternal boolSort

builtinString ::
    InternalVariable variable =>
    Text ->
    TermLike variable
builtinString = Builtin.String.asInternal stringSort

emptyMetadataTools :: SmtMetadataTools Attribute.Symbol
emptyMetadataTools =
    Mock.makeMetadataTools
        [] -- attributesMapping
        [] -- headTypeMapping
        [] -- sortAttributesMapping
        emptySmtDeclarations
        Map.empty -- sortConstructors

metadataTools :: HasCallStack => SmtMetadataTools Attribute.Symbol
metadataTools =
    Mock.makeMetadataTools
        attributesMapping
        sortAttributesMapping
        headSortsMapping
        smtDeclarations
        sortConstructors

axiomSimplifiers :: BuiltinAndAxiomSimplifierMap
axiomSimplifiers = Map.empty

predicateSimplifier ::
    MonadSimplify simplifier => ConditionSimplifier simplifier
predicateSimplifier =
    Simplifier.Condition.create SubstitutionSimplifier.substitutionSimplifier

sortGraph :: SortGraph.SortGraph
sortGraph =
    SortGraph.fromSubsorts
        [Subsort{subsort, supersort} | (subsort, supersort) <- subsorts]

injSimplifier :: InjSimplifier
injSimplifier = mkInjSimplifier sortGraph

overloadGraph :: OverloadGraph.OverloadGraph
overloadGraph = OverloadGraph.fromOverloads overloads

overloadSimplifier :: OverloadSimplifier
overloadSimplifier = mkOverloadSimplifier overloadGraph injSimplifier

env :: MonadSimplify simplifier => Env simplifier
env =
    Env
        { metadataTools = Test.Kore.Step.MockSymbols.metadataTools
        , simplifierCondition = predicateSimplifier
        , simplifierAxioms = axiomSimplifiers
        , memo = Memo.forgetful
        , injSimplifier
        , overloadSimplifier
        }

generatorSetup :: ConsistentKore.Setup
generatorSetup =
    ConsistentKore.Setup
        { allSymbols = filter doesNotHaveArguments symbols
        , allAliases = []
        , allSorts = map fst sortAttributesMapping
        , freeElementVariables = Set.empty
        , freeSetVariables = Set.empty
        , maybeIntSort = Just intSort
        , maybeBoolSort = Just boolSort
        , maybeListSorts =
            Just
                ConsistentKore.CollectionSorts
                    { collectionSort = listSort
                    , elementSort = testSort
                    }
        , maybeMapSorts = Nothing
        , -- TODO(virgil): fill the maybeMapSorts field after implementing
          -- map generators.
          maybeSetSorts = Nothing
        , -- TODO(virgil): fill the maybeSetSorts field after implementing
          -- map generators
          maybeStringLiteralSort = Just stringMetaSort
        , maybeStringBuiltinSort = Just stringSort
        , metadataTools = metadataTools
        }
  where
    doesNotHaveArguments Symbol{symbolParams} = null symbolParams

builtinSimplifiers :: BuiltinAndAxiomSimplifierMap
builtinSimplifiers =
    Map.fromList
        [
            ( AxiomIdentifier.Application unitMapId
            , Builtin.functionEvaluator Map.evalUnit
            )
        ,
            ( AxiomIdentifier.Application elementMapId
            , Builtin.functionEvaluator Map.evalElement
            )
        ,
            ( AxiomIdentifier.Application concatMapId
            , Builtin.functionEvaluator Map.evalConcat
            )
        ,
            ( AxiomIdentifier.Application unitSetId
            , Builtin.functionEvaluator Set.evalUnit
            )
        ,
            ( AxiomIdentifier.Application elementSetId
            , Builtin.functionEvaluator Set.evalElement
            )
        ,
            ( AxiomIdentifier.Application concatSetId
            , Builtin.functionEvaluator Set.evalConcat
            )
        ,
            ( AxiomIdentifier.Application unitListId
            , Builtin.functionEvaluator List.evalUnit
            )
        ,
            ( AxiomIdentifier.Application elementListId
            , Builtin.functionEvaluator List.evalElement
            )
        ,
            ( AxiomIdentifier.Application concatListId
            , Builtin.functionEvaluator List.evalConcat
            )
        ,
            ( AxiomIdentifier.Application tdivIntId
            , builtinEvaluation
                (Builtin.Int.builtinFunctions Map.! Builtin.Int.tdivKey)
            )
        ,
            ( AxiomIdentifier.Application lessIntId
            , builtinEvaluation
                (Builtin.Int.builtinFunctions Map.! Builtin.Int.ltKey)
            )
        ,
            ( AxiomIdentifier.Application greaterEqIntId
            , builtinEvaluation
                (Builtin.Int.builtinFunctions Map.! Builtin.Int.geKey)
            )
        ,
            ( AxiomIdentifier.Application keqBoolId
            , builtinEvaluation
                (Builtin.KEqual.builtinFunctions Map.! Builtin.KEqual.eqKey)
            )
        ]
