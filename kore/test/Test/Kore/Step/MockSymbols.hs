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
   * functional constructors are called "functionallConstr<n><k>"
   * functional symbols are called "functional<n><k>"
   * symbols without any special attribute are called "plain<n><k>"
   * variables are called x, y, z...
-}

import qualified Data.Default as Default
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Data.Sup
import           Kore.ASTHelpers
                 ( ApplicationSorts (ApplicationSorts) )
import qualified Kore.ASTHelpers as ApplicationSorts
                 ( ApplicationSorts (..) )
import           Kore.Attribute.Hook
                 ( Hook (..) )
import qualified Kore.Attribute.Sort as Attribute
import qualified Kore.Attribute.Sort.Concat as Attribute
import qualified Kore.Attribute.Sort.Element as Attribute
import qualified Kore.Attribute.Sort.Unit as Attribute
import           Kore.Attribute.Symbol
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin.Bool as Builtin.Bool
import qualified Kore.Builtin.Int as Builtin.Int
import qualified Kore.Domain.Builtin as Domain
import           Kore.IndexedModule.MetadataTools
                 ( HeadType, SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Internal.TermLike
                 ( TermLike )
import qualified Kore.Internal.TermLike as Internal
import           Kore.Sort
import           Kore.Step.Simplification.Data
                 ( Env (..) )
import qualified Kore.Step.SMT.AST as SMT
import qualified Kore.Step.SMT.Representation.Resolve as SMT
                 ( resolve )
import           Kore.Syntax.Application
import           Kore.Syntax.Variable
import qualified SMT.AST as SMT
import qualified SMT.SimpleSMT as SMT

import           Test.Kore
                 ( testId )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

aId :: Id
aId = testId "a"
aSort0Id :: Id
aSort0Id = testId "aSort0"
aSort1Id :: Id
aSort1Id = testId "aSort1"
aSubsortId :: Id
aSubsortId = testId "aSubsort"
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
gId :: Id
gId = testId "g"
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
constr10Id :: Id
constr10Id = testId "constr10"
constr11Id :: Id
constr11Id = testId "constr11"
constr20Id :: Id
constr20Id = testId "constr20"
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
functionalConstr10Id :: Id
functionalConstr10Id = testId "functionalConstr10"
functionalConstr11Id :: Id
functionalConstr11Id = testId "functionalConstr11"
functionalConstr12Id :: Id
functionalConstr12Id = testId "functionalConstr12"
functionalConstr20Id :: Id
functionalConstr20Id = testId "functionalConstr20"
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

aSymbol :: SymbolOrAlias
aSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = aId
    , symbolOrAliasParams      = []
    }
aSort0Symbol :: SymbolOrAlias
aSort0Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = aSort0Id
    , symbolOrAliasParams      = []
    }
aSort1Symbol :: SymbolOrAlias
aSort1Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = aSort1Id
    , symbolOrAliasParams      = []
    }
aSubsortSymbol :: SymbolOrAlias
aSubsortSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = aSubsortId
    , symbolOrAliasParams      = []
    }
aSubSubsortSymbol :: SymbolOrAlias
aSubSubsortSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = aSubSubsortId
    , symbolOrAliasParams      = []
    }
aTopSortSymbol :: SymbolOrAlias
aTopSortSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = aTopSortId
    , symbolOrAliasParams      = []
    }
aOtherSortSymbol :: SymbolOrAlias
aOtherSortSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = aOtherSortId
    , symbolOrAliasParams      = []
    }
bSymbol :: SymbolOrAlias
bSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = bId
    , symbolOrAliasParams      = []
    }
bSort0Symbol :: SymbolOrAlias
bSort0Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = bSort0Id
    , symbolOrAliasParams      = []
    }
cSymbol :: SymbolOrAlias
cSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = cId
    , symbolOrAliasParams      = []
    }
dSymbol :: SymbolOrAlias
dSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = dId
    , symbolOrAliasParams      = []
    }
eSymbol :: SymbolOrAlias
eSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = eId
    , symbolOrAliasParams      = []
    }
fSymbol :: SymbolOrAlias
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = fId
    , symbolOrAliasParams      = []
    }
gSymbol :: SymbolOrAlias
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = gId
    , symbolOrAliasParams      = []
    }
hSymbol :: SymbolOrAlias
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = hId
    , symbolOrAliasParams      = []
    }
cfSymbol :: SymbolOrAlias
cfSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = cfId
    , symbolOrAliasParams      = []
    }
cfSort0Symbol :: SymbolOrAlias
cfSort0Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = cfSort0Id
    , symbolOrAliasParams      = []
    }
cfSort1Symbol :: SymbolOrAlias
cfSort1Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = cfSort1Id
    , symbolOrAliasParams      = []
    }
cgSymbol :: SymbolOrAlias
cgSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = cgId
    , symbolOrAliasParams      = []
    }
cgSort0Symbol :: SymbolOrAlias
cgSort0Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = cgSort0Id
    , symbolOrAliasParams      = []
    }
chSymbol :: SymbolOrAlias
chSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = chId
    , symbolOrAliasParams      = []
    }
plain00Symbol :: SymbolOrAlias
plain00Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain00Id
    , symbolOrAliasParams      = []
    }
plain00Sort0Symbol :: SymbolOrAlias
plain00Sort0Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain00Sort0Id
    , symbolOrAliasParams      = []
    }
plain00SubsortSymbol :: SymbolOrAlias
plain00SubsortSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain00SubsortId
    , symbolOrAliasParams      = []
    }
plain00SubSubsortSymbol :: SymbolOrAlias
plain00SubSubsortSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain00SubSubsortId
    , symbolOrAliasParams      = []
    }
plain10Symbol :: SymbolOrAlias
plain10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain10Id
    , symbolOrAliasParams      = []
    }
plain11Symbol :: SymbolOrAlias
plain11Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain11Id
    , symbolOrAliasParams      = []
    }
plain20Symbol :: SymbolOrAlias
plain20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain20Id
    , symbolOrAliasParams      = []
    }
constr10Symbol :: SymbolOrAlias
constr10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = constr10Id
    , symbolOrAliasParams      = []
    }
constr11Symbol :: SymbolOrAlias
constr11Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = constr11Id
    , symbolOrAliasParams      = []
    }
constr20Symbol :: SymbolOrAlias
constr20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = constr20Id
    , symbolOrAliasParams      = []
    }
function20MapTestSymbol :: SymbolOrAlias
function20MapTestSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = function20MapTestId
    , symbolOrAliasParams      = []
    }
functional00Symbol :: SymbolOrAlias
functional00Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional00Id
    , symbolOrAliasParams      = []
    }
functional01Symbol :: SymbolOrAlias
functional01Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional01Id
    , symbolOrAliasParams      = []
    }
functional10Symbol :: SymbolOrAlias
functional10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional10Id
    , symbolOrAliasParams      = []
    }
functional11Symbol :: SymbolOrAlias
functional11Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional11Id
    , symbolOrAliasParams      = []
    }
functional20Symbol :: SymbolOrAlias
functional20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional20Id
    , symbolOrAliasParams      = []
    }
functional00SubSubSortSymbol :: SymbolOrAlias
functional00SubSubSortSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional00SubSubSortId
    , symbolOrAliasParams      = []
    }
functionalConstr10Symbol :: SymbolOrAlias
functionalConstr10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalConstr10Id
    , symbolOrAliasParams      = []
    }
functionalConstr11Symbol :: SymbolOrAlias
functionalConstr11Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalConstr11Id
    , symbolOrAliasParams      = []
    }
functionalConstr12Symbol :: SymbolOrAlias
functionalConstr12Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalConstr12Id
    , symbolOrAliasParams      = []
    }
functionalConstr20Symbol :: SymbolOrAlias
functionalConstr20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalConstr20Id
    , symbolOrAliasParams      = []
    }
functionalConstr30Symbol :: SymbolOrAlias
functionalConstr30Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalConstr30Id
    , symbolOrAliasParams      = []
    }
functionalTopConstr20Symbol :: SymbolOrAlias
functionalTopConstr20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalTopConstr20Id
    , symbolOrAliasParams      = []
    }
functionalTopConstr21Symbol :: SymbolOrAlias
functionalTopConstr21Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalTopConstr21Id
    , symbolOrAliasParams      = []
    }
injective10Symbol :: SymbolOrAlias
injective10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = injective10Id
    , symbolOrAliasParams      = []
    }
injective11Symbol :: SymbolOrAlias
injective11Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = injective11Id
    , symbolOrAliasParams      = []
    }
sortInjection10Symbol :: SymbolOrAlias
sortInjection10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = sortInjectionId
    , symbolOrAliasParams      = [testSort0, testSort]
    }
sortInjection11Symbol :: SymbolOrAlias
sortInjection11Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = sortInjectionId
    , symbolOrAliasParams      = [testSort1, testSort]
    }
sortInjection0ToTopSymbol :: SymbolOrAlias
sortInjection0ToTopSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = sortInjectionId
    , symbolOrAliasParams      = [testSort0, topSort]
    }
sortInjectionSubToTopSymbol :: SymbolOrAlias
sortInjectionSubToTopSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = sortInjectionId
    , symbolOrAliasParams      = [subSort, topSort]
    }
sortInjectionSubSubToTopSymbol :: SymbolOrAlias
sortInjectionSubSubToTopSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = sortInjectionId
    , symbolOrAliasParams      = [subSubsort, topSort]
    }
sortInjectionSubSubToSubSymbol :: SymbolOrAlias
sortInjectionSubSubToSubSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = sortInjectionId
    , symbolOrAliasParams      = [subSubsort, subSort]
    }
sortInjectionOtherToTopSymbol :: SymbolOrAlias
sortInjectionOtherToTopSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = sortInjectionId
    , symbolOrAliasParams      = [otherSort, topSort]
    }
unitMapSymbol :: SymbolOrAlias
unitMapSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = unitMapId
    , symbolOrAliasParams      = []
    }
elementMapSymbol :: SymbolOrAlias
elementMapSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = elementMapId
    , symbolOrAliasParams      = []
    }
concatMapSymbol :: SymbolOrAlias
concatMapSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = concatMapId
    , symbolOrAliasParams      = []
    }
lessIntSymbol :: SymbolOrAlias
lessIntSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = lessIntId
    , symbolOrAliasParams      = []
    }
greaterEqIntSymbol :: SymbolOrAlias
greaterEqIntSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = greaterEqIntId
    , symbolOrAliasParams      = []
    }

concatListSymbol :: SymbolOrAlias
concatListSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = concatListId
    , symbolOrAliasParams = []
    }

elementListSymbol :: SymbolOrAlias
elementListSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = elementListId
    , symbolOrAliasParams = []
    }

unitListSymbol :: SymbolOrAlias
unitListSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = unitListId
    , symbolOrAliasParams = []
    }

concatSetSymbol :: SymbolOrAlias
concatSetSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = concatSetId
    , symbolOrAliasParams = []
    }

elementSetSymbol :: SymbolOrAlias
elementSetSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = elementSetId
    , symbolOrAliasParams = []
    }

unitSetSymbol :: SymbolOrAlias
unitSetSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = unitSetId
    , symbolOrAliasParams = []
    }

sigmaSymbol :: SymbolOrAlias
sigmaSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = sigmaId
    , symbolOrAliasParams      = []
    }

var_x_1 :: Variable
var_x_1 = Variable (testId "x") (Just (Element 1)) testSort
var_y_1 :: Variable
var_y_1 = Variable (testId "y") (Just (Element 1)) testSort
var_z_1 :: Variable
var_z_1 = Variable (testId "z") (Just (Element 1)) testSort
x :: Variable
x = Variable (testId "x") mempty testSort
y :: Variable
y = Variable (testId "y") mempty testSort
z :: Variable
z = Variable (testId "z") mempty testSort
m :: Variable
m = Variable (testId "m") mempty mapSort
xSet :: Variable
xSet = Variable (testId "xSet") mempty setSort
xInt :: Variable
xInt = Variable (testId "xInt") mempty intSort
xSubSort :: Variable
xSubSort = Variable (testId "xSubSort") mempty subSort
xTopSort :: Variable
xTopSort = Variable (testId "xTopSort") mempty topSort

a :: Ord variable => TermLike variable
a = Internal.mkApp testSort aSymbol []

aConcrete :: TermLike Concrete
Just aConcrete = Internal.asConcrete (a :: TermLike Variable)

aSort0 :: Ord variable => TermLike variable
aSort0 = Internal.mkApp testSort0 aSort0Symbol []

aSort1 :: Ord variable => TermLike variable
aSort1 = Internal.mkApp testSort1 aSort1Symbol []

aSubsort :: Ord variable => TermLike variable
aSubsort = Internal.mkApp subSort aSubsortSymbol []

aSubSubsort :: Ord variable => TermLike variable
aSubSubsort = Internal.mkApp subSubsort aSubSubsortSymbol []

aTopSort :: Ord variable => TermLike variable
aTopSort = Internal.mkApp topSort aTopSortSymbol []

aOtherSort :: Ord variable => TermLike variable
aOtherSort = Internal.mkApp otherSort aOtherSortSymbol []

b :: Ord variable => TermLike variable
b = Internal.mkApp testSort bSymbol []

bConcrete :: TermLike Concrete
Just bConcrete = Internal.asConcrete (b :: TermLike Variable)

bSort0 :: Ord variable => TermLike variable
bSort0 = Internal.mkApp testSort0 bSort0Symbol []

c :: Ord variable => TermLike variable
c = Internal.mkApp testSort cSymbol []

d :: Ord variable => TermLike variable
d = Internal.mkApp testSort dSymbol []

e :: Ord variable => TermLike variable
e = Internal.mkApp testSort eSymbol []

f, g, h
    :: Ord variable
    => TermLike variable
    -> TermLike variable
f arg = Internal.mkApp testSort fSymbol [arg]
g arg = Internal.mkApp testSort gSymbol [arg]
h arg = Internal.mkApp testSort hSymbol [arg]

cf :: Ord variable => TermLike variable
cf = Internal.mkApp testSort cfSymbol []

cfSort0 :: Ord variable => TermLike variable
cfSort0 = Internal.mkApp testSort0 cfSort0Symbol []

cfSort1 :: Ord variable => TermLike variable
cfSort1 = Internal.mkApp testSort1 cfSort1Symbol []

cg :: Ord variable => TermLike variable
cg = Internal.mkApp testSort cgSymbol []

cgSort0 :: Ord variable => TermLike variable
cgSort0 = Internal.mkApp testSort0 cgSort0Symbol []

ch :: Ord variable => TermLike variable
ch = Internal.mkApp testSort chSymbol []

plain00 :: Ord variable => TermLike variable
plain00 = Internal.mkApp testSort plain00Symbol []

plain00Sort0 :: Ord variable => TermLike variable
plain00Sort0 = Internal.mkApp testSort0 plain00Sort0Symbol []

plain00Subsort :: Ord variable => TermLike variable
plain00Subsort = Internal.mkApp subSort plain00SubsortSymbol []

plain00SubSubsort :: Ord variable => TermLike variable
plain00SubSubsort = Internal.mkApp subSubsort plain00SubSubsortSymbol []

plain10, plain11
    :: Ord variable
    => TermLike variable
    -> TermLike variable
plain10 arg = Internal.mkApp testSort plain10Symbol [arg]
plain11 arg = Internal.mkApp testSort plain11Symbol [arg]

plain20
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
plain20 arg1 arg2 = Internal.mkApp testSort plain20Symbol [arg1, arg2]

constr10, constr11
    :: Ord variable
    => TermLike variable
    -> TermLike variable
constr10 arg = Internal.mkApp testSort constr10Symbol [arg]
constr11 arg = Internal.mkApp testSort constr11Symbol [arg]

constr20
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
constr20 arg1 arg2 = Internal.mkApp testSort constr20Symbol [arg1, arg2]

function20MapTest
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
function20MapTest arg1 arg2 =
    Internal.mkApp testSort function20MapTestSymbol [arg1, arg2]

functional00 :: Ord variable => TermLike variable
functional00 = Internal.mkApp testSort functional00Symbol []

functional01 :: Ord variable => TermLike variable
functional01 = Internal.mkApp testSort functional01Symbol []

functional10
    :: Ord variable
    => TermLike variable
    -> TermLike variable
functional10 arg = Internal.mkApp testSort functional10Symbol [arg]

functional11
    :: Ord variable
    => TermLike variable
    -> TermLike variable
functional11 arg = Internal.mkApp testSort functional11Symbol [arg]

functional20
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functional20 arg1 arg2 = Internal.mkApp testSort functional20Symbol [arg1, arg2]

functional00SubSubSort :: Ord variable => TermLike variable
functional00SubSubSort =
    Internal.mkApp subSubsort functional00SubSubSortSymbol []

functionalConstr10
    :: Ord variable
    => TermLike variable
    -> TermLike variable
functionalConstr10 arg =
    Internal.mkApp testSort functionalConstr10Symbol [arg]

functionalConstr11
    :: Ord variable
    => TermLike variable
    -> TermLike variable
functionalConstr11 arg = Internal.mkApp testSort functionalConstr11Symbol [arg]

functionalConstr12
    :: Ord variable
    => TermLike variable
    -> TermLike variable
functionalConstr12 arg = Internal.mkApp testSort functionalConstr12Symbol [arg]

functionalConstr20
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalConstr20 arg1 arg2 =
    Internal.mkApp testSort functionalConstr20Symbol [arg1, arg2]

functionalConstr30
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalConstr30 arg1 arg2 arg3 =
    Internal.mkApp testSort functionalConstr30Symbol [arg1, arg2, arg3]

functionalTopConstr20
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalTopConstr20 arg1 arg2 =
    Internal.mkApp testSort functionalTopConstr20Symbol [arg1, arg2]

functionalTopConstr21
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
functionalTopConstr21 arg1 arg2 =
    Internal.mkApp testSort functionalTopConstr21Symbol [arg1, arg2]

injective10
    :: Ord variable
    => TermLike variable
    -> TermLike variable
injective10 arg = Internal.mkApp testSort injective10Symbol [arg]

injective11
    :: Ord variable
    => TermLike variable
    -> TermLike variable
injective11 arg = Internal.mkApp testSort injective11Symbol [arg]

sortInjection10
    :: Ord variable
    => TermLike variable
    -> TermLike variable
sortInjection10 arg =
    Internal.mkApp testSort sortInjection10Symbol [arg]

sortInjection11
    :: Ord variable
    => TermLike variable
    -> TermLike variable
sortInjection11 arg =
    Internal.mkApp testSort sortInjection11Symbol [arg]

sortInjection0ToTop
    :: Ord variable
    => TermLike variable
    -> TermLike variable
sortInjection0ToTop arg =
    Internal.mkApp topSort sortInjection0ToTopSymbol [arg]

sortInjectionSubToTop
    :: Ord variable
    => TermLike variable
    -> TermLike variable
sortInjectionSubToTop arg =
    Internal.mkApp topSort sortInjectionSubToTopSymbol [arg]

sortInjectionSubSubToTop
    :: Ord variable
    => TermLike variable
    -> TermLike variable
sortInjectionSubSubToTop arg =
    Internal.mkApp topSort sortInjectionSubSubToTopSymbol [arg]

sortInjectionSubSubToSub
    :: Ord variable
    => TermLike variable
    -> TermLike variable
sortInjectionSubSubToSub arg =
    Internal.mkApp subSort sortInjectionSubSubToSubSymbol [arg]

sortInjectionOtherToTop
    :: Ord variable
    => TermLike variable
    -> TermLike variable
sortInjectionOtherToTop arg =
    Internal.mkApp topSort sortInjectionOtherToTopSymbol [arg]

unitMap
    :: Ord variable
    => TermLike variable
unitMap = Internal.mkApp mapSort unitMapSymbol []

elementMap
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
elementMap m1 m2 = Internal.mkApp mapSort elementMapSymbol [m1, m2]

concatMap
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
concatMap m1 m2 = Internal.mkApp mapSort concatMapSymbol [m1, m2]

unitSet
    :: Ord variable
    => TermLike variable
unitSet = Internal.mkApp setSort unitSetSymbol []

elementSet
    :: Ord variable
    => TermLike variable
    -> TermLike variable
elementSet s1 = Internal.mkApp setSort elementSetSymbol [s1]

concatSet
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
concatSet s1 s2 = Internal.mkApp setSort concatSetSymbol [s1, s2]

lessInt
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
lessInt i1 i2 = Internal.mkApp boolSort lessIntSymbol [i1, i2]

greaterEqInt
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
greaterEqInt i1 i2 = Internal.mkApp boolSort greaterEqIntSymbol [i1, i2]

concatList
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
concatList l1 l2 = Internal.mkApp listSort concatListSymbol [l1, l2]

sigma
    :: Ord variable
    => TermLike variable
    -> TermLike variable
    -> TermLike variable
sigma child1 child2 = Internal.mkApp testSort sigmaSymbol [child1, child2]

attributesMapping :: [(SymbolOrAlias, StepperAttributes)]
attributesMapping =
    [   ( aSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( aSort0Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( aSort1Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( aSubsortSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( aSubSubsortSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( aTopSortSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( aOtherSortSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( bSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( bSort0Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( cSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( dSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( eSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( fSymbol
        , Mock.functionAttributes
        )
    ,   ( gSymbol
        , Mock.functionAttributes
        )
    ,   ( hSymbol
        , Mock.functionAttributes
        )
    ,   ( cfSymbol
        , Mock.functionAttributes
        )
    ,   ( cfSort0Symbol
        , Mock.functionAttributes
        )
    ,   ( cfSort1Symbol
        , Mock.functionAttributes
        )
    ,   ( cgSymbol
        , Mock.functionAttributes
        )
    ,   ( cgSort0Symbol
        , Mock.functionAttributes
        )
    ,   ( chSymbol
        , Mock.functionAttributes
        )
    ,   ( plain00Symbol
        , Mock.defaultAttributes
        )
    ,   ( plain00Sort0Symbol
        , Mock.defaultAttributes
        )
    ,   ( plain00SubsortSymbol
        , Mock.defaultAttributes
        )
    ,   ( plain00SubSubsortSymbol
        , Mock.defaultAttributes
        )
    ,   ( plain10Symbol
        , Mock.defaultAttributes
        )
    ,   ( plain11Symbol
        , Mock.defaultAttributes
        )
    ,   ( plain20Symbol
        , Mock.defaultAttributes
        )
    ,   ( constr10Symbol
        , Mock.constructorAttributes
        )
    ,   ( constr11Symbol
        , Mock.constructorAttributes
        )
    ,   ( constr20Symbol
        , Mock.constructorAttributes
        )
    ,   ( function20MapTestSymbol
        , Mock.functionAttributes
        )
    ,   ( functional00Symbol
        , Mock.functionalAttributes
        )
    ,   ( functional01Symbol
        , Mock.functionalAttributes
        )
    ,   ( functional10Symbol
        , Mock.functionalAttributes
        )
    ,   ( functional11Symbol
        , Mock.functionalAttributes
        )
    ,   ( functional20Symbol
        , Mock.functionalAttributes
        )
    ,   ( functional00SubSubSortSymbol
        , Mock.functionalAttributes
        )
    ,   ( functionalConstr10Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( functionalConstr11Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( functionalConstr12Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( functionalConstr20Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( functionalConstr30Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( functionalTopConstr20Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( functionalTopConstr21Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( injective10Symbol
        , Mock.injectiveAttributes
        )
    ,   ( injective11Symbol
        , Mock.injectiveAttributes
        )
    ,   ( sortInjection10Symbol
        , Mock.sortInjectionAttributes
        )
    ,   ( sortInjection11Symbol
        , Mock.sortInjectionAttributes
        )
    ,   ( sortInjection0ToTopSymbol
        , Mock.sortInjectionAttributes
        )
    ,   ( sortInjectionSubToTopSymbol
        , Mock.sortInjectionAttributes
        )
    ,   ( sortInjectionSubSubToTopSymbol
        , Mock.sortInjectionAttributes
        )
    ,   ( sortInjectionSubSubToSubSymbol
        , Mock.sortInjectionAttributes
        )
    ,   ( sortInjectionOtherToTopSymbol
        , Mock.sortInjectionAttributes
        )
    ,   ( unitMapSymbol
        , Mock.functionalAttributes { hook = Hook (Just "MAP.unit") }
        )
    ,   ( elementMapSymbol
        , Mock.functionalAttributes { hook = Hook (Just "MAP.element") }
        )
    ,   ( concatMapSymbol
        , Mock.functionalAttributes { hook = Hook (Just "MAP.concat") }
        )
    ,   ( concatListSymbol
        , Mock.functionalAttributes { hook = Hook (Just "LIST.concat") }
        )
    ,   ( elementListSymbol
        , Mock.functionalAttributes { hook = Hook (Just "LIST.element") }
        )
    ,   ( unitListSymbol
        , Mock.functionalAttributes { hook = Hook (Just "LIST.unit") }
        )
    ,   ( concatSetSymbol
        , Mock.functionalAttributes { hook = Hook (Just "SET.concat") }
        )
    ,   ( elementSetSymbol
        , Mock.functionalAttributes { hook = Hook (Just "SET.element") }
        )
    ,   ( unitSetSymbol
        , Mock.functionalAttributes { hook = Hook (Just "SET.unit") }
        )
    ,   ( lessIntSymbol
        , Mock.functionalAttributes
            { hook = Hook (Just "INT.lt")
            , smthook = Smthook (Just (SMT.Atom "<"))
            }
        )
    ,   ( greaterEqIntSymbol
        , Mock.functionalAttributes
            { hook = Hook (Just "INT.ge")
            , smthook = Smthook (Just (SMT.Atom ">="))
            }
        )
    ,   ( sigmaSymbol
        , Mock.constructorFunctionalAttributes
        )
    ]

headTypeMapping :: [(SymbolOrAlias, HeadType)]
headTypeMapping =
    [   ( aSymbol
        , HeadType.Symbol
        )
    ,   ( aSort0Symbol
        , HeadType.Symbol
        )
    ,   ( aSort1Symbol
        , HeadType.Symbol
        )
    ,   ( aSubsortSymbol
        , HeadType.Symbol
        )
    ,   ( aSubSubsortSymbol
        , HeadType.Symbol
        )
    ,   ( aTopSortSymbol
        , HeadType.Symbol
        )
    ,   ( aOtherSortSymbol
        , HeadType.Symbol
        )
    ,   ( bSymbol
        , HeadType.Symbol
        )
    ,   ( bSort0Symbol
        , HeadType.Symbol
        )
    ,   ( cSymbol
        , HeadType.Symbol
        )
    ,   ( dSymbol
        , HeadType.Symbol
        )
    ,   ( eSymbol
        , HeadType.Symbol
        )
    ,   ( fSymbol
        , HeadType.Symbol
        )
    ,   ( gSymbol
        , HeadType.Symbol
        )
    ,   ( hSymbol
        , HeadType.Symbol
        )
    ,   ( cfSymbol
        , HeadType.Symbol
        )
    ,   ( cfSort0Symbol
        , HeadType.Symbol
        )
    ,   ( cfSort1Symbol
        , HeadType.Symbol
        )
    ,   ( cgSymbol
        , HeadType.Symbol
        )
    ,   ( cgSort0Symbol
        , HeadType.Symbol
        )
    ,   ( chSymbol
        , HeadType.Symbol
        )
    ,   ( plain00Symbol
        , HeadType.Symbol
        )
    ,   ( plain00Sort0Symbol
        , HeadType.Symbol
        )
    ,   ( plain00SubsortSymbol
        , HeadType.Symbol
        )
    ,   ( plain00SubSubsortSymbol
        , HeadType.Symbol
        )
    ,   ( plain10Symbol
        , HeadType.Symbol
        )
    ,   ( plain11Symbol
        , HeadType.Symbol
        )
    ,   ( plain20Symbol
        , HeadType.Symbol
        )
    ,   ( constr10Symbol
        , HeadType.Symbol
        )
    ,   ( constr11Symbol
        , HeadType.Symbol
        )
    ,   ( constr20Symbol
        , HeadType.Symbol
        )
    ,   ( function20MapTestSymbol
        , HeadType.Symbol
        )
    ,   ( functional00Symbol
        , HeadType.Symbol
        )
    ,   ( functional01Symbol
        , HeadType.Symbol
        )
    ,   ( functional10Symbol
        , HeadType.Symbol
        )
    ,   ( functional11Symbol
        , HeadType.Symbol
        )
    ,   ( functional20Symbol
        , HeadType.Symbol
        )
    ,   ( functional00SubSubSortSymbol
        , HeadType.Symbol
        )
    ,   ( functionalConstr10Symbol
        , HeadType.Symbol
        )
    ,   ( functionalConstr11Symbol
        , HeadType.Symbol
        )
    ,   ( functionalConstr12Symbol
        , HeadType.Symbol
        )
    ,   ( functionalConstr20Symbol
        , HeadType.Symbol
        )
    ,   ( functionalConstr30Symbol
        , HeadType.Symbol
        )
    ,   ( functionalTopConstr20Symbol
        , HeadType.Symbol
        )
    ,   ( functionalTopConstr21Symbol
        , HeadType.Symbol
        )
    ,   ( injective10Symbol
        , HeadType.Symbol
        )
    ,   ( injective11Symbol
        , HeadType.Symbol
        )
    ,   ( sortInjection10Symbol
        , HeadType.Symbol
        )
    ,   ( sortInjection11Symbol
        , HeadType.Symbol
        )
    ,   ( sortInjection0ToTopSymbol
        , HeadType.Symbol
        )
    ,   ( sortInjectionSubToTopSymbol
        , HeadType.Symbol
        )
    ,   ( sortInjectionSubSubToTopSymbol
        , HeadType.Symbol
        )
    ,   ( sortInjectionSubSubToSubSymbol
        , HeadType.Symbol
        )
    ,   ( sortInjectionOtherToTopSymbol
        , HeadType.Symbol
        )
    ,   ( unitMapSymbol
        , HeadType.Symbol
        )
    ,   ( elementMapSymbol
        , HeadType.Symbol
        )
    ,   ( concatMapSymbol
        , HeadType.Symbol
        )
    ,   ( elementListSymbol
        , HeadType.Symbol
        )
    ,   ( unitListSymbol
        , HeadType.Symbol
        )
    ,   ( concatListSymbol
        , HeadType.Symbol
        )
    ,   ( elementSetSymbol
        , HeadType.Symbol
        )
    ,   ( unitSetSymbol
        , HeadType.Symbol
        )
    ,   ( concatSetSymbol
        , HeadType.Symbol
        )
    ,   ( lessIntSymbol
        , HeadType.Symbol
        )
    ,   ( greaterEqIntSymbol
        , HeadType.Symbol
        )
    ,   ( sigmaSymbol
        , HeadType.Symbol
        )
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
    ,   ( subSubsort
        , Default.def
        )
    ,   ( otherSort
        , Default.def
        )
    ,   ( mapSort
        , Default.def
            { Attribute.hook = Hook (Just "MAP.Map")
            , Attribute.unit = Attribute.Unit (Just unitMapSymbol)
            , Attribute.element = Attribute.Element (Just elementMapSymbol)
            , Attribute.concat = Attribute.Concat (Just concatMapSymbol)
            }
        )
    ,   ( listSort
        , Default.def
            { Attribute.hook = Hook (Just "LIST.List")
            , Attribute.unit = Attribute.Unit (Just unitListSymbol)
            , Attribute.element = Attribute.Element (Just elementListSymbol)
            , Attribute.concat = Attribute.Concat (Just concatListSymbol)
            }
        )
    ,   ( setSort
        , Default.def
            { Attribute.hook = Hook (Just "SET.Set")
            , Attribute.unit = Attribute.Unit (Just unitSetSymbol)
            , Attribute.element = Attribute.Element (Just elementSetSymbol)
            , Attribute.concat = Attribute.Concat (Just concatSetSymbol)
            }
        )
    ,   ( intSort
        , Default.def { Attribute.hook = Hook (Just "INT.Int") }
        )
    ,   ( boolSort
        , Default.def { Attribute.hook = Hook (Just "BOOL.Bool") }
        )
    ]

headSortsMapping :: [(SymbolOrAlias, ApplicationSorts)]
headSortsMapping =
    [   ( aSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( aSort0Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort0
            }
        )
    ,   ( aSort1Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort1
            }
        )
    ,   ( aSubsortSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = subSort
            }
        )
    ,   ( aSubSubsortSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = subSubsort
            }
        )
    ,   ( aTopSortSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = topSort
            }
        )
    ,   ( aOtherSortSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = otherSort
            }
        )
    ,   ( bSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( bSort0Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort0
            }
        )
    ,   ( cSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( dSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( eSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( fSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult   = testSort
            }
        )
    ,   ( gSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult   = testSort
            }
        )
    ,   ( hSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult   = testSort
            }
        )
    ,   ( cfSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( cfSort0Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort0
            }
        )
    ,   ( cfSort1Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort1
            }
        )
    ,   ( cgSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( cgSort0Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort0
            }
        )
    ,   ( chSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( plain00Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort
            }
        )
    ,   ( plain00Sort0Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = testSort0
            }
        )
    ,   ( plain00SubsortSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = subSort
            }
        )
    ,   ( plain00SubSubsortSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult   = subSubsort
            }
        )
    ,   ( plain10Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult   = testSort
            }
        )
    ,   ( plain11Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult   = testSort
            }
        )
    ,   ( plain20Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort, testSort]
            , applicationSortsResult   = testSort
            }
        )
    ,   ( constr10Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( constr11Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( constr20Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort, testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( function20MapTestSymbol
        , ApplicationSorts
             { applicationSortsOperands = [mapSort, testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functional00Symbol
        , ApplicationSorts
             { applicationSortsOperands = []
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functional01Symbol
        , ApplicationSorts
             { applicationSortsOperands = []
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functional10Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functional11Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functional20Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort, testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functional00SubSubSortSymbol
        , ApplicationSorts
             { applicationSortsOperands = []
             , applicationSortsResult   = subSubsort
             }
        )
    ,   ( functionalConstr10Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functionalConstr11Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functionalConstr12Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functionalConstr20Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort, testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functionalConstr30Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort, testSort, testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functionalTopConstr20Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort, testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( functionalTopConstr21Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort, testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( injective10Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( injective11Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( sortInjection10Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort0]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( sortInjection11Symbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort1]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( sortInjection0ToTopSymbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort0]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( sortInjectionSubToTopSymbol
        , ApplicationSorts
             { applicationSortsOperands = [subSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( sortInjectionSubSubToTopSymbol
        , ApplicationSorts
             { applicationSortsOperands = [subSubsort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( sortInjectionSubSubToSubSymbol
        , ApplicationSorts
             { applicationSortsOperands = [subSubsort]
             , applicationSortsResult   = subSort
             }
        )
    ,   ( sortInjectionOtherToTopSymbol
        , ApplicationSorts
             { applicationSortsOperands = [otherSort]
             , applicationSortsResult   = testSort
             }
        )
    ,   ( unitMapSymbol
        , ApplicationSorts
             { applicationSortsOperands = []
             , applicationSortsResult   = mapSort
             }
        )
    ,   ( elementMapSymbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = mapSort
             }
        )
    ,   ( concatMapSymbol
        , ApplicationSorts
             { applicationSortsOperands = [mapSort, mapSort]
             , applicationSortsResult   = mapSort
             }
        )
    ,   ( elementListSymbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort]
             , applicationSortsResult   = listSort
             }
        )
    ,   ( unitListSymbol
        , ApplicationSorts
             { applicationSortsOperands = []
             , applicationSortsResult   = listSort
             }
        )
    ,   ( concatListSymbol
        , ApplicationSorts
             { applicationSortsOperands = [listSort, listSort]
             , applicationSortsResult   = listSort
             }
        )
    ,   ( elementSetSymbol
        , ApplicationSorts
             { applicationSortsOperands = [setSort]
             , applicationSortsResult   = setSort
             }
        )
    ,   ( unitSetSymbol
        , ApplicationSorts
             { applicationSortsOperands = []
             , applicationSortsResult   = setSort
             }
        )
    ,   ( concatSetSymbol
        , ApplicationSorts
             { applicationSortsOperands = [setSort, setSort]
             , applicationSortsResult   = setSort
             }
        )
    ,   ( lessIntSymbol
        , ApplicationSorts
             { applicationSortsOperands = [intSort, intSort]
             , applicationSortsResult   = boolSort
             }
        )
    ,   ( greaterEqIntSymbol
        , ApplicationSorts
             { applicationSortsOperands = [intSort, intSort]
             , applicationSortsResult   = boolSort
             }
        )
    ,   ( sigmaSymbol
        , ApplicationSorts
             { applicationSortsOperands = [testSort, testSort]
             , applicationSortsResult   = testSort
             }
        )
    ]

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
            SMT.SymbolDeclaredIndirectly SMT.IndirectSymbolDeclaration
                { name = encodableId
                , sorts = map SMT.SortReference (resultSort : argumentSorts)
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
            SMT.SymbolDeclaredIndirectly SMT.IndirectSymbolDeclaration
                { name = SMT.AlreadyEncoded builtin
                , sorts = map SMT.SortReference (resultSort : argumentSorts)
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
        [ (aId, smtConstructor aId [] testSort)
        , ( aSort0Id, smtConstructor aSort0Id [] testSort1)
        , ( aSort1Id, smtConstructor aSort1Id [] testSort1)
        , ( aSubsortId, smtConstructor aSubsortId [] subSort)
        , ( aSubSubsortId, smtConstructor aSubSubsortId [] subSubsort)
        , ( aTopSortId, smtConstructor aTopSortId [] topSort)
        , ( aOtherSortId, smtConstructor aOtherSortId [] otherSort)
        , ( bId, smtConstructor bId [] testSort)
        , ( bSort0Id, smtConstructor bSort0Id [] testSort0)
        , ( cId, smtConstructor cId [] testSort)
        , ( dId, smtConstructor dId [] testSort)
        , ( eId, smtConstructor eId [] testSort)
        , ( constr10Id, smtConstructor constr10Id [testSort] testSort)
        , ( constr11Id, smtConstructor constr11Id [testSort] testSort)
        , ( constr20Id, smtConstructor constr20Id [testSort, testSort] testSort)
        ,   ( functionalConstr10Id
            , smtConstructor functionalConstr10Id [testSort] testSort
            )
        ,   ( functionalConstr11Id
            , smtConstructor functionalConstr11Id [testSort] testSort
            )
        ,   ( functionalConstr12Id
            , smtConstructor functionalConstr12Id [testSort] testSort
            )
        ,   ( functionalConstr20Id
            , smtConstructor functionalConstr20Id [testSort, testSort] testSort
            )
        ,   ( functionalConstr30Id
            , smtConstructor
                functionalConstr30Id
                [testSort, testSort, testSort]
                testSort
            )
        ,   ( functionalTopConstr20Id
            , smtConstructor
                functionalTopConstr21Id [testSort, testSort] testSort
            )
        ,   ( functionalTopConstr21Id
            , smtConstructor
                functionalTopConstr21Id [testSort, testSort] testSort
            )
        , ( lessIntId, smtBuiltinSymbol "<" [intSort, intSort] boolSort)
        , ( greaterEqIntId, smtBuiltinSymbol ">=" [intSort, intSort] boolSort)
        , ( sigmaId, smtConstructor sigmaId [testSort, testSort] testSort)
        ]
    }

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
subSubsortId :: Id
subSubsortId = testId "subSubsort"
otherSortId :: Id
otherSortId = testId "otherSort"
intSortId :: Id
intSortId = testId "intSort"
boolSortId :: Id
boolSortId = testId "boolSort"

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
    , (otherSort, topSort)
    ]

builtinMap
    :: Ord variable
    => [(TermLike Concrete, TermLike variable)]
    -> TermLike variable
builtinMap child =
    Internal.mkBuiltin $ Domain.BuiltinMap Domain.InternalMap
        { builtinMapSort = mapSort
        , builtinMapUnit = unitMapSymbol
        , builtinMapElement = elementMapSymbol
        , builtinMapConcat = concatMapSymbol
        , builtinMapChild = Map.fromList child
        }

builtinList
    :: Ord variable
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
    :: Ord variable
    => [TermLike Concrete]
    -> TermLike variable
builtinSet child =
    Internal.mkBuiltin $ Domain.BuiltinSet Domain.InternalSet
        { builtinSetSort = setSort
        , builtinSetUnit = unitSetSymbol
        , builtinSetElement = elementSetSymbol
        , builtinSetConcat = concatSetSymbol
        , builtinSetChild = Set.fromList child
        }

builtinInt
    :: Ord variable
    => Integer
    -> TermLike variable
builtinInt = Builtin.Int.asInternal intSort

builtinBool
    :: Ord variable
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
        [] -- headSortsMapping
        emptySmtDeclarations

metadataTools :: SmtMetadataTools Attribute.Symbol
metadataTools =
    Mock.makeMetadataTools
        attributesMapping
        headTypeMapping
        sortAttributesMapping
        subsorts
        headSortsMapping
        smtDeclarations

env :: Env
env = Env { metadataTools = Test.Kore.Step.MockSymbols.metadataTools }
