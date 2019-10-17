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

import Control.Applicative
import qualified Control.Lens as Lens
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Default as Default
import qualified Data.Either as Either
import Data.Function
import Data.Generics.Product
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified GHC.Stack as GHC

import Data.Sup
import Kore.Attribute.Hook
    ( Hook (..)
    )
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Concat as Attribute
import qualified Kore.Attribute.Sort.Constructors as Attribute
    ( Constructors
    )
import qualified Kore.Attribute.Sort.Element as Attribute
import qualified Kore.Attribute.Sort.Unit as Attribute
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Int as Builtin.Int
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.ApplicationSorts
    ( ApplicationSorts
    )
import Kore.Internal.Symbol
import Kore.Internal.TermLike
    ( InternalVariable
    , TermLike
    )
import qualified Kore.Internal.TermLike as Internal
import Kore.Sort
import qualified Kore.Step.Function.Memo as Memo
import Kore.Step.Simplification.Data
    ( Env (Env)
    , MonadSimplify
    )
import qualified Kore.Step.Simplification.Data as SimplificationData.DoNotUse
import qualified Kore.Step.Simplification.Predicate as Simplifier.Predicate
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import Kore.Step.Simplification.Simplify
    ( BuiltinAndAxiomSimplifierMap
    , PredicateSimplifier
    , TermLikeSimplifier
    )
import qualified Kore.Step.SMT.AST as SMT
import qualified Kore.Step.SMT.Representation.Resolve as SMT
    ( resolve
    )
import Kore.Syntax.Application
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
import Kore.Variables.UnifiedVariable
import qualified SMT.AST as SMT
import qualified SMT.SimpleSMT as SMT

import qualified Test.ConsistentKore as ConsistentKore
    ( CollectionSorts (..)
    , Setup (..)
    )
import Test.Kore
    ( testId
    )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

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
fTestIntId :: Id
fTestIntId = testId "fTestInt"
plain00Id :: Id
plain00Id = testId "plain00"
plain00Sort0Id :: Id
plain00Sort0Id = testId "plain00Sort0"
plain00SubsortId :: Id
plain00SubsortId = testId "plain00Subsort"
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
elementSetId :: Id
elementSetId = testId "elementSet"
unitSetId :: Id
unitSetId = testId "unitSet"
sigmaId :: Id
sigmaId = testId "sigma"
anywhereId :: Id
anywhereId = testId "anywhere"

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

fTestIntSymbol :: Symbol
fTestIntSymbol = symbol fTestIntId [testSort] intSort & function

plain00Symbol :: Symbol
plain00Symbol = symbol plain00Id [] testSort

plain00Sort0Symbol :: Symbol
plain00Sort0Symbol = symbol plain00Sort0Id [] testSort0

plain00SubsortSymbol :: Symbol
plain00SubsortSymbol = symbol plain00SubsortId [] subSort

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
    & constructor & function

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
    & functional & constructor

functionalConstr21Symbol :: Symbol
functionalConstr21Symbol =
    symbol functionalConstr21Id [testSort, testSort] testSort
    & functional & constructor

functionalConstr30Symbol :: Symbol
functionalConstr30Symbol =
    symbol functionalConstr30Id [testSort, testSort, testSort] testSort
    & functional & constructor

functionalTopConstr20Symbol :: Symbol
functionalTopConstr20Symbol =
    symbol functionalTopConstr20Id [topSort, testSort] testSort
    & functional & constructor

functionalTopConstr21Symbol :: Symbol
functionalTopConstr21Symbol =
    symbol functionalTopConstr21Id [testSort, topSort] testSort
    & functional & constructor

injective10Symbol :: Symbol
injective10Symbol = symbol injective10Id [testSort] testSort & injective

injective11Symbol :: Symbol
injective11Symbol = symbol injective11Id [testSort] testSort & injective

sortInjectionSymbol :: Sort -> Sort -> Symbol
sortInjectionSymbol fromSort toSort = Symbol
    { symbolConstructor = sortInjectionId
    , symbolParams      = [fromSort, toSort]
    , symbolAttributes  = Mock.sortInjectionAttributes
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

sortInjectionOtherToTopSymbol :: Symbol
sortInjectionOtherToTopSymbol = sortInjectionSymbol otherSort topSort

unitMapSymbol :: Symbol
unitMapSymbol =
    symbol unitMapId [] mapSort
    & functional & hook "MAP.unit"

elementMapSymbol :: Symbol
elementMapSymbol =
    symbol elementMapId [testSort, testSort] mapSort
    & functional & hook "MAP.element"

concatMapSymbol :: Symbol
concatMapSymbol =
    symbol concatMapId [mapSort, mapSort] mapSort
    & functional & hook "MAP.concat"

lessIntSymbol :: Symbol
lessIntSymbol =
    symbol lessIntId [intSort, intSort] boolSort
    & functional & hook "INT.lt" & smthook "<"

greaterEqIntSymbol :: Symbol
greaterEqIntSymbol =
    symbol greaterEqIntId [intSort, intSort] boolSort
    & functional & hook "INT.ge" & smthook ">="

tdivIntSymbol :: Symbol
tdivIntSymbol =
    symbol tdivIntId [intSort, intSort] intSort
    & function & hook "INT.tdiv"

concatListSymbol :: Symbol
concatListSymbol =
    symbol concatListId [listSort, listSort] listSort
    & functional & hook "LIST.concat"

elementListSymbol :: Symbol
elementListSymbol =
    symbol elementListId [testSort] listSort
    & functional & hook "LIST.element"

unitListSymbol :: Symbol
unitListSymbol = symbol unitListId [] listSort & functional & hook "LIST.unit"

concatSetSymbol :: Symbol
concatSetSymbol =
    symbol concatSetId [setSort, setSort] setSort
    & functional & hook "SET.concat"

elementSetSymbol :: Symbol
elementSetSymbol =
    symbol elementSetId [testSort] setSort & functional & hook "SET.element"

unitSetSymbol :: Symbol
unitSetSymbol =
    symbol unitSetId [] setSort & functional & hook "SET.unit"

sigmaSymbol :: Symbol
sigmaSymbol =
    symbol sigmaId [testSort, testSort] testSort
    & functional & constructor

anywhereSymbol :: Symbol
anywhereSymbol =
    symbol anywhereId [] testSort
    & functional
    & Lens.set
        (typed @Attribute.Symbol . typed @Attribute.Anywhere)
        (Attribute.Anywhere True)

var_x_0 :: ElementVariable Variable
var_x_0 = ElementVariable $ Variable (testId "x") (Just (Element 0)) testSort
var_x_1 :: ElementVariable Variable
var_x_1 = ElementVariable $ Variable (testId "x") (Just (Element 1)) testSort
var_y_1 :: ElementVariable Variable
var_y_1 = ElementVariable $ Variable (testId "y") (Just (Element 1)) testSort
var_z_1 :: ElementVariable Variable
var_z_1 = ElementVariable $ Variable (testId "z") (Just (Element 1)) testSort
x :: ElementVariable Variable
x = ElementVariable $ Variable (testId "x") mempty testSort
setX :: SetVariable Variable
setX = SetVariable $ Variable (testId "@x") mempty testSort
var_setX_0 :: SetVariable Variable
var_setX_0 = SetVariable $ Variable (testId "@x") (Just (Element 0)) testSort
x0 :: ElementVariable Variable
x0 = ElementVariable $ Variable (testId "x0") mempty testSort0
y :: ElementVariable Variable
y = ElementVariable $ Variable (testId "y") mempty testSort
setY :: SetVariable Variable
setY = SetVariable $ Variable (testId "@y") mempty testSort
z :: ElementVariable Variable
z = ElementVariable $ Variable (testId "z") mempty testSort
t :: ElementVariable Variable
t = ElementVariable $ Variable (testId "t") mempty testSort
u :: ElementVariable Variable
u = ElementVariable $ Variable (testId "u") mempty testSort
m :: ElementVariable Variable
m = ElementVariable $ Variable (testId "m") mempty mapSort
xSet :: ElementVariable Variable
xSet = ElementVariable $ Variable (testId "xSet") mempty setSort
ySet :: ElementVariable Variable
ySet = ElementVariable $ Variable (testId "ySet") mempty setSort
xInt :: ElementVariable Variable
xInt = ElementVariable $ Variable (testId "xInt") mempty intSort
yInt :: ElementVariable Variable
yInt = ElementVariable $ Variable (testId "yInt") mempty intSort
xBool :: ElementVariable Variable
xBool = ElementVariable $ Variable (testId "xBool") mempty boolSort
xString :: ElementVariable Variable
xString = ElementVariable $ Variable (testId "xString") mempty stringSort
xList :: ElementVariable Variable
xList = ElementVariable $ Variable (testId "xList") mempty listSort
xMap :: ElementVariable Variable
xMap = ElementVariable $ Variable (testId "xMap") mempty mapSort
xSubSort :: ElementVariable Variable
xSubSort = ElementVariable $ Variable (testId "xSubSort") mempty subSort
xSubSubSort :: ElementVariable Variable
xSubSubSort =
    ElementVariable $ Variable (testId "xSubSubSort") mempty subSubsort
xTopSort :: ElementVariable Variable
xTopSort = ElementVariable $ Variable (testId "xTopSort") mempty topSort

makeUnifiedVariable :: Text -> Sort -> UnifiedVariable Variable
makeUnifiedVariable v sort
  | Text.head v == '@' = SetVar (SetVariable v')
  | otherwise = ElemVar (ElementVariable v')
  where
    v' = Variable
        { variableSort = sort
        , variableName = testId v
        , variableCounter = mempty
        }

makeTestUnifiedVariable :: Text -> UnifiedVariable Variable
makeTestUnifiedVariable = (`makeUnifiedVariable` testSort)

mkTestUnifiedVariable :: Text -> TermLike Variable
mkTestUnifiedVariable = Internal.mkVar . makeTestUnifiedVariable

a :: InternalVariable variable => TermLike variable
a = Internal.mkApplySymbol aSymbol []

aConcrete :: TermLike Concrete
Just aConcrete = Internal.asConcrete (a :: TermLike Variable)

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
Just bConcrete = Internal.asConcrete (b :: TermLike Variable)

bSort0 :: InternalVariable variable => TermLike variable
bSort0 = Internal.mkApplySymbol bSort0Symbol []

c :: InternalVariable variable => TermLike variable
c = Internal.mkApplySymbol cSymbol []

d :: InternalVariable variable => TermLike variable
d = Internal.mkApplySymbol dSymbol []

e :: InternalVariable variable => TermLike variable
e = Internal.mkApplySymbol eSymbol []

f, g, h
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
f arg = Internal.mkApplySymbol fSymbol [arg]
g arg = Internal.mkApplySymbol gSymbol [arg]
h arg = Internal.mkApplySymbol hSymbol [arg]

fSort0, gSort0
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
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

fSet
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
fSet arg = Internal.mkApplySymbol fSetSymbol [arg]

fTestInt
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
fTestInt arg = Internal.mkApplySymbol fTestIntSymbol [arg]

fInt
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
fInt arg = Internal.mkApplySymbol fIntSymbol [arg]

plain00 :: InternalVariable variable => TermLike variable
plain00 = Internal.mkApplySymbol plain00Symbol []

plain00Sort0 :: InternalVariable variable => TermLike variable
plain00Sort0 = Internal.mkApplySymbol plain00Sort0Symbol []

plain00Subsort :: InternalVariable variable => TermLike variable
plain00Subsort = Internal.mkApplySymbol plain00SubsortSymbol []

plain00SubSubsort :: InternalVariable variable => TermLike variable
plain00SubSubsort = Internal.mkApplySymbol plain00SubSubsortSymbol []

plain10, plain11
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
plain10 arg = Internal.mkApplySymbol plain10Symbol [arg]
plain11 arg = Internal.mkApplySymbol plain11Symbol [arg]

plain20
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
plain20 arg1 arg2 = Internal.mkApplySymbol plain20Symbol [arg1, arg2]

constr00 :: InternalVariable variable => GHC.HasCallStack => TermLike variable
constr00 = Internal.mkApplySymbol constr00Symbol []

constr10, constr11
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
constr10 arg = Internal.mkApplySymbol constr10Symbol [arg]
constr11 arg = Internal.mkApplySymbol constr11Symbol [arg]

constr20
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
constr20 arg1 arg2 = Internal.mkApplySymbol constr20Symbol [arg1, arg2]

constrFunct20TestMap
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
constrFunct20TestMap arg1 arg2 =
    Internal.mkApplySymbol constrFunct20TestMapSymbol [arg1, arg2]

function20MapTest
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
function20MapTest arg1 arg2 =
    Internal.mkApplySymbol function20MapTestSymbol [arg1, arg2]

functional00 :: InternalVariable variable => TermLike variable
functional00 = Internal.mkApplySymbol functional00Symbol []

functional01 :: InternalVariable variable => TermLike variable
functional01 = Internal.mkApplySymbol functional01Symbol []

functional10
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
functional10 arg = Internal.mkApplySymbol functional10Symbol [arg]

functional11
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
functional11 arg = Internal.mkApplySymbol functional11Symbol [arg]

functional20
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functional20 arg1 arg2 = Internal.mkApplySymbol functional20Symbol [arg1, arg2]

functional00SubSubSort :: InternalVariable variable => TermLike variable
functional00SubSubSort =
    Internal.mkApplySymbol functional00SubSubSortSymbol []

functionalInjective00
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
functionalInjective00 =
    Internal.mkApplySymbol functionalInjective00Symbol []

functionalConstr10
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
functionalConstr10 arg =
    Internal.mkApplySymbol functionalConstr10Symbol [arg]

functionalConstr11
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
functionalConstr11 arg = Internal.mkApplySymbol functionalConstr11Symbol [arg]

functionalConstr12
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
functionalConstr12 arg = Internal.mkApplySymbol functionalConstr12Symbol [arg]

functionalConstr20
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalConstr20 arg1 arg2 =
    Internal.mkApplySymbol functionalConstr20Symbol [arg1, arg2]

functionalConstr21
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalConstr21 arg1 arg2 =
    Internal.mkApplySymbol functionalConstr21Symbol [arg1, arg2]

functionalConstr30
    :: InternalVariable variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalConstr30 arg1 arg2 arg3 =
    Internal.mkApplySymbol functionalConstr30Symbol [arg1, arg2, arg3]

functionalTopConstr20
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalTopConstr20 arg1 arg2 =
    Internal.mkApplySymbol functionalTopConstr20Symbol [arg1, arg2]

functionalTopConstr21
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalTopConstr21 arg1 arg2 =
    Internal.mkApplySymbol functionalTopConstr21Symbol [arg1, arg2]

injective10
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
injective10 arg = Internal.mkApplySymbol injective10Symbol [arg]

injective11
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
injective11 arg = Internal.mkApplySymbol injective11Symbol [arg]

sortInjection
    :: InternalVariable variable
    => GHC.HasCallStack
    => Sort
    -> TermLike variable
    -> TermLike variable
sortInjection toSort termLike =
    Internal.mkApplySymbol (sortInjectionSymbol fromSort toSort) [termLike]
  where
    fromSort = Internal.termLikeSort termLike

sortInjection10
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjection10 arg = Internal.mkApplySymbol sortInjection10Symbol [arg]

sortInjection11
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjection11 arg = Internal.mkApplySymbol sortInjection11Symbol [arg]

sortInjection0ToTop
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjection0ToTop arg =
    Internal.mkApplySymbol sortInjection0ToTopSymbol [arg]

sortInjectionSubToTop
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjectionSubToTop arg =
    Internal.mkApplySymbol sortInjectionSubToTopSymbol [arg]

sortInjectionSubSubToTop
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjectionSubSubToTop arg =
    Internal.mkApplySymbol sortInjectionSubSubToTopSymbol [arg]

sortInjectionSubSubToSub
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjectionSubSubToSub arg =
    Internal.mkApplySymbol sortInjectionSubSubToSubSymbol [arg]

sortInjectionSubSubToOther
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjectionSubSubToOther arg =
    Internal.mkApplySymbol sortInjectionSubSubToOtherSymbol [arg]

sortInjectionSubOtherToOther
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjectionSubOtherToOther arg =
    Internal.mkApplySymbol sortInjectionSubOtherToOtherSymbol [arg]

sortInjectionOtherToTop
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
sortInjectionOtherToTop arg =
    Internal.mkApplySymbol sortInjectionOtherToTopSymbol [arg]

unitMap :: InternalVariable variable => TermLike variable
unitMap = Internal.mkApplySymbol unitMapSymbol []

elementMap
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
elementMap m1 m2 = Internal.mkApplySymbol elementMapSymbol [m1, m2]

concatMap
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
concatMap m1 m2 = Internal.mkApplySymbol concatMapSymbol [m1, m2]

unitSet :: InternalVariable variable => TermLike variable
unitSet = Internal.mkApplySymbol unitSetSymbol []

elementSet
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
elementSet s1 = Internal.mkApplySymbol elementSetSymbol [s1]

concatSet
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
concatSet s1 s2 = Internal.mkApplySymbol concatSetSymbol [s1, s2]

lessInt
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
lessInt i1 i2 = Internal.mkApplySymbol lessIntSymbol [i1, i2]

greaterEqInt
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
greaterEqInt i1 i2 = Internal.mkApplySymbol greaterEqIntSymbol [i1, i2]

tdivInt
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
tdivInt i1 i2 = Internal.mkApplySymbol tdivIntSymbol [i1, i2]

concatList
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
concatList l1 l2 = Internal.mkApplySymbol concatListSymbol [l1, l2]

elementList
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
elementList element = Internal.mkApplySymbol elementListSymbol [element]

sigma
    :: InternalVariable variable
    => GHC.HasCallStack
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
sigma child1 child2 = Internal.mkApplySymbol sigmaSymbol [child1, child2]

anywhere :: InternalVariable variable => TermLike variable
anywhere = Internal.mkApplySymbol anywhereSymbol []

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
    , sortInjectionOtherToTopSymbol
    , unitMapSymbol
    , elementMapSymbol
    , concatMapSymbol
    , concatListSymbol
    , elementListSymbol
    , unitListSymbol
    , concatSetSymbol
    , elementSetSymbol
    , unitSetSymbol
    , lessIntSymbol
    , greaterEqIntSymbol
    , tdivIntSymbol
    , sigmaSymbol
    , anywhereSymbol
    ]

sortAttributesMapping :: [(Sort, Attribute.Sort)]
sortAttributesMapping =
    [   ( testSort
        , Default.def
        )
    ,   ( testSort0
        , Default.def
        )
    ,   ( testSort1
        , Default.def
        )
    ,   ( topSort
        , Default.def
        )
    ,   ( subSort
        , Default.def
        )
    ,   ( subOthersort
        , Default.def
        )
    ,   ( subSubsort
        , Default.def
        )
    ,   ( otherSort
        , Default.def
        )
    ,   ( mapSort
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
    ,   ( listSort
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
    ,   ( setSort
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
    ,   ( intSort
        , Default.def { Attribute.hook = Hook (Just "INT.Int") }
        )
    ,   ( boolSort
        , Default.def { Attribute.hook = Hook (Just "BOOL.Bool") }
        )

    -- Also add attributes for the implicitly defined sorts.
    ,   ( stringMetaSort
        , Default.def { Attribute.hook = Hook (Just "STRING.String") }
        )
    ]

headSortsMapping :: [(SymbolOrAlias, ApplicationSorts)]
headSortsMapping =
    map ((,) <$> toSymbolOrAlias <*> symbolSorts) symbols

zeroarySmtSort :: Id -> SMT.UnresolvedSort
zeroarySmtSort sortId =
    SMT.Sort
        { smtFromSortArgs = const (const (Just (SMT.Atom encodedId)))
        , declaration = SMT.SortDeclarationSort SMT.SortDeclaration
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
        , declaration =
            SMT.SortDeclaredIndirectly
                (SMT.AlreadyEncoded (SMT.nameFromSExpr sExpr))
        }

smtConstructor :: Id -> [Sort] -> Sort -> SMT.UnresolvedSymbol
smtConstructor symbolId argumentSorts resultSort =
    SMT.Symbol
        { smtFromSortArgs = const (const (Just (SMT.Atom encodedId)))
        , declaration =
            SMT.SymbolConstructor SMT.IndirectSymbolDeclaration
                { name = encodableId
                , resultSort = SMT.SortReference resultSort
                , argumentSorts = map SMT.SortReference argumentSorts
                }
        }
  where
    encodableId = SMT.encodable symbolId
    encodedId = SMT.encode encodableId

smtBuiltinSymbol
    :: Text -> [Sort] -> Sort -> SMT.UnresolvedSymbol
smtBuiltinSymbol builtin argumentSorts resultSort =
    SMT.Symbol
        { smtFromSortArgs = const (const (Just (SMT.Atom builtin)))
        , declaration =
            SMT.SymbolBuiltin SMT.IndirectSymbolDeclaration
                { name = SMT.AlreadyEncoded builtin
                , resultSort = SMT.SortReference resultSort
                , argumentSorts = map SMT.SortReference argumentSorts
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
smtUnresolvedDeclarations = SMT.Declarations
    { sorts = Map.fromList
        [ (testSort0Id, zeroarySmtSort testSort0Id)
        , (testSort1Id, zeroarySmtSort testSort1Id)
        , (topSortId, zeroarySmtSort topSortId)
        , (topSortId, zeroarySmtSort subSortId)
        , (topSortId, zeroarySmtSort subSubsortId)
        , (topSortId, zeroarySmtSort otherSortId)
        -- TODO(virgil): testSort has constructors, it should have a
        -- constructor-based definition. The same for others.
        , (testSortId, zeroarySmtSort testSortId)
        , (intSortId, builtinZeroarySmtSort SMT.tInt)
        , (boolSortId, builtinZeroarySmtSort SMT.tBool)
        ]
    , symbols = Map.fromList
        [ ( aSort0Id, smtConstructor aSort0Id [] testSort1)
        , ( aSort1Id, smtConstructor aSort1Id [] testSort1)
        , ( aSubsortId, smtConstructor aSubsortId [] subSort)
        , ( aSubOthersortId, smtConstructor aSubOthersortId [] subSubsort)
        , ( aSubSubsortId, smtConstructor aSubSubsortId [] subSubsort)
        , ( aTopSortId, smtConstructor aTopSortId [] topSort)
        , ( aOtherSortId, smtConstructor aOtherSortId [] otherSort)
        , ( bSort0Id, smtConstructor bSort0Id [] testSort0)
        , ( lessIntId, smtBuiltinSymbol "<" [intSort, intSort] boolSort)
        , ( greaterEqIntId, smtBuiltinSymbol ">=" [intSort, intSort] boolSort)
        , ( sigmaId, smtConstructor sigmaId [testSort, testSort] testSort)
        ]
    }

sortConstructors :: Map.Map Id Attribute.Constructors
sortConstructors = Map.fromList
    [
    -- TODO(virgil): testSort has constructors, it should have a
    -- constructor-based definition. The same for others.
    ]

testSortId :: Id
testSortId = testId "testSort"
testSort0Id :: Id
testSort0Id = testId "testSort0"
testSort1Id :: Id
testSort1Id = testId "testSort1"
topSortId :: Id
topSortId = testId "topSort"
subSortId :: Id
subSortId = testId "subSort"
subOthersortId :: Id
subOthersortId = testId "subOthersort"
subSubsortId :: Id
subSubsortId = testId "subSubsort"
otherSortId :: Id
otherSortId = testId "otherSort"
intSortId :: Id
intSortId = testId "intSort"
boolSortId :: Id
boolSortId = testId "boolSort"
stringSortId :: Id
stringSortId = testId "stringSort"

testSort :: Sort
testSort =
    SortActualSort SortActual
        { sortActualName  = testSortId
        , sortActualSorts = []
        }

testSort0 :: Sort
testSort0 =
    SortActualSort SortActual
        { sortActualName  = testSort0Id
        , sortActualSorts = []
        }

testSort1 :: Sort
testSort1 =
    SortActualSort SortActual
        { sortActualName  = testSort1Id
        , sortActualSorts = []
        }

topSort :: Sort
topSort =
    SortActualSort SortActual
        { sortActualName  = topSortId
        , sortActualSorts = []
        }

subSort :: Sort
subSort =
    SortActualSort SortActual
        { sortActualName  = subSortId
        , sortActualSorts = []
        }

subOthersort :: Sort
subOthersort =
    SortActualSort SortActual
        { sortActualName  = subOthersortId
        , sortActualSorts = []
        }

subSubsort :: Sort
subSubsort =
    SortActualSort SortActual
        { sortActualName  = subSubsortId
        , sortActualSorts = []
        }

otherSort :: Sort
otherSort =
    SortActualSort SortActual
        { sortActualName = otherSortId
        , sortActualSorts = []
        }

mapSort :: Sort
mapSort =
    SortActualSort SortActual
        { sortActualName  = testId "mapSort"
        , sortActualSorts = []
        }

setSort :: Sort
setSort =
    SortActualSort SortActual
        { sortActualName  = testId "setSort"
        , sortActualSorts = []
        }

listSort :: Sort
listSort =
    SortActualSort SortActual
        { sortActualName  = testId "listSort"
        , sortActualSorts = []
        }

intSort :: Sort
intSort =
    SortActualSort SortActual
        { sortActualName  = intSortId
        , sortActualSorts = []
        }

stringSort :: Sort
stringSort =
    SortActualSort SortActual
        { sortActualName  = stringSortId
        , sortActualSorts = []
        }

boolSort :: Sort
boolSort =
    SortActualSort SortActual
        { sortActualName  = boolSortId
        , sortActualSorts = []
        }

subsorts :: [(Sort, Sort)]
subsorts =
    [ (subSubsort, subSort)
    , (subSubsort, topSort)
    , (subSort, topSort)
    , (subSubsort, otherSort)
    , (subOthersort, otherSort)
    , (otherSort, topSort)
    ]

builtinMap
    :: InternalVariable variable
    => [(TermLike variable, TermLike variable)]
    -> TermLike variable
builtinMap elements = framedMap elements []

framedMap
    :: InternalVariable variable
    => [(TermLike variable, TermLike variable)]
    -> [ElementVariable variable]
    -> TermLike variable
framedMap elements (map Internal.mkElemVar -> opaque) =
    Internal.mkBuiltin $ Domain.BuiltinMap Domain.InternalAc
        { builtinAcSort = mapSort
        , builtinAcUnit = unitMapSymbol
        , builtinAcElement = elementMapSymbol
        , builtinAcConcat = concatMapSymbol
        , builtinAcChild = Domain.NormalizedMap Domain.NormalizedAc
            { elementsWithVariables = Domain.wrapElement <$> abstractElements
            , concreteElements
            , opaque
            }
        }
  where
    asConcrete element@(key, value) =
        (,) <$> Internal.asConcrete key <*> pure value
        & maybe (Left element) Right
    (abstractElements, Map.fromList -> concreteElements) =
        asConcrete . Bifunctor.second Domain.MapValue <$> elements
        & Either.partitionEithers

builtinList
    :: InternalVariable variable
    => [TermLike variable]
    -> TermLike variable
builtinList child =
    Internal.mkBuiltin $ Domain.BuiltinList Domain.InternalList
        { builtinListSort = listSort
        , builtinListUnit = unitListSymbol
        , builtinListElement = elementListSymbol
        , builtinListConcat = concatListSymbol
        , builtinListChild = Seq.fromList child
        }

builtinSet
    :: InternalVariable variable
    => [TermLike Concrete]
    -> TermLike variable
builtinSet child =
    Internal.mkBuiltin $ Domain.BuiltinSet Domain.InternalAc
        { builtinAcSort = setSort
        , builtinAcUnit = unitSetSymbol
        , builtinAcElement = elementSetSymbol
        , builtinAcConcat = concatSetSymbol
        , builtinAcChild = Domain.NormalizedSet Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements =
                Map.fromList (map (\key -> (key, Domain.SetValue)) child)
            , opaque = []
            }
        }

builtinInt
    :: InternalVariable variable
    => Integer
    -> TermLike variable
builtinInt = Builtin.Int.asInternal intSort

builtinBool
    :: InternalVariable variable
    => Bool
    -> TermLike variable
builtinBool = Builtin.Bool.asInternal boolSort

emptyMetadataTools :: SmtMetadataTools Attribute.Symbol
emptyMetadataTools =
    Mock.makeMetadataTools
        [] -- attributesMapping
        [] -- headTypeMapping
        [] -- sortAttributesMapping
        [] -- subsorts
        emptySmtDeclarations
        Map.empty -- sortConstructors

metadataTools :: GHC.HasCallStack => SmtMetadataTools Attribute.Symbol
metadataTools =
    Mock.makeMetadataTools
        attributesMapping
        sortAttributesMapping
        subsorts
        headSortsMapping
        smtDeclarations
        sortConstructors

termLikeSimplifier :: TermLikeSimplifier
termLikeSimplifier = Simplifier.create

axiomSimplifiers :: BuiltinAndAxiomSimplifierMap
axiomSimplifiers = Map.empty

predicateSimplifier
    :: MonadSimplify simplifier => PredicateSimplifier simplifier
predicateSimplifier = Simplifier.Predicate.create

env :: MonadSimplify simplifier => Env simplifier
env =
    Env
        { metadataTools = Test.Kore.Step.MockSymbols.metadataTools
        , simplifierTermLike = termLikeSimplifier
        , simplifierPredicate = predicateSimplifier
        , simplifierAxioms = axiomSimplifiers
        , memo = Memo.forgetful
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
        , maybeListSorts = Just ConsistentKore.CollectionSorts
            { collectionSort = listSort
            , elementSort = testSort
            }
        , maybeMapSorts = Nothing
        -- TODO(virgil): fill the maybeMapSorts field after implementing
        -- map generators.
        , maybeSetSorts = Nothing
        -- TODO(virgil): fill the maybeSetSorts field after implementing
        -- map generators
        , maybeStringLiteralSort = Just stringMetaSort
        , maybeStringBuiltinSort = Just stringSort
        , metadataTools = metadataTools
        }
  where
    doesNotHaveArguments Symbol {symbolParams} = null symbolParams
