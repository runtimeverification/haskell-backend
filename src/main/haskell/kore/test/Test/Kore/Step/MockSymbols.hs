module Test.Kore.Step.MockSymbols where

-- Intended usage:
-- * Import qualified.
-- * use sortToolsMapping and attributesMapping to build mock SortTools and
--   MetadataTools.
-- * Use things like a, b, c, x, y, z for testing.

-- RULES:
-- * Everything that does not obey the default rules must be clearly
--   specified in the name, e.g. 'constantNotFunctional'.
-- * constant symbols are, by default, functional.
-- * constant functions are called cf, cg, ch.
-- * constant constructors are called a, b, c, ...
-- * one-element functions are called f, g, h.
-- * constructors are called "constr<n><k>" where n is the arity and k is used
--   to differentiate between them (both are one-digit).
-- * functional constructors are called "functionallConstr<n><k>"
-- * functional symbols are called "functional<n><k>"
-- * symbols without any special attribute are called "plain<n><k>"
-- * variables are called x, y, z...

import Data.Reflection
       ( Given )

import           Kore.AST.Common
                 ( Id (..), Sort (..), SortActual (..), SymbolOrAlias (..),
                 Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkApp )
import           Kore.IndexedModule.MetadataTools
                 ( SortTools )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( constructorAttributes, constructorFunctionalAttributes,
                 defaultAttributes, functionAttributes, functionalAttributes )


import Test.Kore
       ( testId )

aId :: Id Object
aId = testId "a"
bId :: Id Object
bId = testId "b"
cId :: Id Object
cId = testId "c"
dId :: Id Object
dId = testId "d"
eId :: Id Object
eId = testId "e"
fId :: Id Object
fId = testId "f"
gId :: Id Object
gId = testId "g"
hId :: Id Object
hId = testId "h"
cfId :: Id Object
cfId = testId "cf"
cgId :: Id Object
cgId = testId "cg"
chId :: Id Object
chId = testId "ch"
plain00Id :: Id Object
plain00Id = testId "plain00"
plain10Id :: Id Object
plain10Id = testId "plain10"
plain20Id :: Id Object
plain20Id = testId "plain20"
constr10Id :: Id Object
constr10Id = testId "constr10"
constr11Id :: Id Object
constr11Id = testId "constr11"
constr20Id :: Id Object
constr20Id = testId "constr20"
functional00Id :: Id Object
functional00Id = testId "functional00"
functional10Id :: Id Object
functional10Id = testId "functional10"
functional11Id :: Id Object
functional11Id = testId "functional11"
functional20Id :: Id Object
functional20Id = testId "functional20"
functionalConstr10Id :: Id Object
functionalConstr10Id = testId "functionalConstr10"
functionalConstr20Id :: Id Object
functionalConstr20Id = testId "functionalConstr20"

aSymbol :: SymbolOrAlias Object
aSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = aId
    , symbolOrAliasParams      = []
    }
bSymbol :: SymbolOrAlias Object
bSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = bId
    , symbolOrAliasParams      = []
    }
cSymbol :: SymbolOrAlias Object
cSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = cId
    , symbolOrAliasParams      = []
    }
dSymbol :: SymbolOrAlias Object
dSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = dId
    , symbolOrAliasParams      = []
    }
eSymbol :: SymbolOrAlias Object
eSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = eId
    , symbolOrAliasParams      = []
    }
fSymbol :: SymbolOrAlias Object
fSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = fId
    , symbolOrAliasParams      = []
    }
gSymbol :: SymbolOrAlias Object
gSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = gId
    , symbolOrAliasParams      = []
    }
hSymbol :: SymbolOrAlias Object
hSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = hId
    , symbolOrAliasParams      = []
    }
cfSymbol :: SymbolOrAlias Object
cfSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = cfId
    , symbolOrAliasParams      = []
    }
cgSymbol :: SymbolOrAlias Object
cgSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = cgId
    , symbolOrAliasParams      = []
    }
chSymbol :: SymbolOrAlias Object
chSymbol = SymbolOrAlias
    { symbolOrAliasConstructor = chId
    , symbolOrAliasParams      = []
    }
plain00Symbol :: SymbolOrAlias Object
plain00Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain00Id
    , symbolOrAliasParams      = []
    }
plain10Symbol :: SymbolOrAlias Object
plain10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain10Id
    , symbolOrAliasParams      = []
    }
plain20Symbol :: SymbolOrAlias Object
plain20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = plain20Id
    , symbolOrAliasParams      = []
    }
constr10Symbol :: SymbolOrAlias Object
constr10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = constr10Id
    , symbolOrAliasParams      = []
    }
constr11Symbol :: SymbolOrAlias Object
constr11Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = constr11Id
    , symbolOrAliasParams      = []
    }
constr20Symbol :: SymbolOrAlias Object
constr20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = constr20Id
    , symbolOrAliasParams      = []
    }
functional00Symbol :: SymbolOrAlias Object
functional00Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional00Id
    , symbolOrAliasParams      = []
    }
functional10Symbol :: SymbolOrAlias Object
functional10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional10Id
    , symbolOrAliasParams      = []
    }
functional11Symbol :: SymbolOrAlias Object
functional11Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional11Id
    , symbolOrAliasParams      = []
    }
functional20Symbol :: SymbolOrAlias Object
functional20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functional20Id
    , symbolOrAliasParams      = []
    }
functionalConstr10Symbol :: SymbolOrAlias Object
functionalConstr10Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalConstr10Id
    , symbolOrAliasParams      = []
    }
functionalConstr20Symbol :: SymbolOrAlias Object
functionalConstr20Symbol = SymbolOrAlias
    { symbolOrAliasConstructor = functionalConstr20Id
    , symbolOrAliasParams      = []
    }

x :: Variable Object
x = Variable (testId "x") testSort
y :: Variable Object
y = Variable (testId "y") testSort
z :: Variable Object
z = Variable (testId "z") testSort

a   :: Given (SortTools Object)
    => PureMLPattern Object variable
a = mkApp aSymbol []

b   :: Given (SortTools Object)
    => PureMLPattern Object variable
b = mkApp bSymbol []

c   :: Given (SortTools Object)
    => PureMLPattern Object variable
c = mkApp cSymbol []

d   :: Given (SortTools Object)
    => PureMLPattern Object variable
d = mkApp dSymbol []

e   :: Given (SortTools Object)
    => PureMLPattern Object variable
e = mkApp eSymbol []

f   :: Given (SortTools Object)
    => PureMLPattern Object variable -> PureMLPattern Object variable
f arg = mkApp fSymbol [arg]

g   :: Given (SortTools Object)
    => PureMLPattern Object variable -> PureMLPattern Object variable
g arg = mkApp gSymbol [arg]

h   :: Given (SortTools Object)
    => PureMLPattern Object variable -> PureMLPattern Object variable
h arg = mkApp hSymbol [arg]

cf  :: Given (SortTools Object)
    => PureMLPattern Object variable
cf = mkApp cfSymbol []

cg  :: Given (SortTools Object)
    => PureMLPattern Object variable
cg = mkApp cgSymbol []

ch  :: Given (SortTools Object)
    => PureMLPattern Object variable
ch = mkApp chSymbol []

plain00
    :: Given (SortTools Object)
    => PureMLPattern Object variable
plain00 = mkApp plain00Symbol []

plain10
    :: Given (SortTools Object)
    => PureMLPattern Object variable -> PureMLPattern Object variable
plain10 arg = mkApp plain10Symbol [arg]

plain20
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
    -> PureMLPattern Object variable
plain20 arg1 arg2 = mkApp plain20Symbol [arg1, arg2]

constr10
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
constr10 arg = mkApp constr10Symbol [arg]

constr11
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
constr11 arg = mkApp constr11Symbol [arg]

constr20
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
    -> PureMLPattern Object variable
constr20 arg1 arg2 = mkApp constr20Symbol [arg1, arg2]

functional00
    :: Given (SortTools Object)
    => PureMLPattern Object variable
functional00 = mkApp functional00Symbol []

functional10
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
functional10 arg = mkApp functional10Symbol [arg]

functional11
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
functional11 arg = mkApp functional11Symbol [arg]

functional20
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
    -> PureMLPattern Object variable
functional20 arg1 arg2 = mkApp functional20Symbol [arg1, arg2]

functionalConstr10
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
functionalConstr10 arg = mkApp functionalConstr10Symbol [arg]

functionalConstr20
    :: Given (SortTools Object)
    => PureMLPattern Object variable
    -> PureMLPattern Object variable
    -> PureMLPattern Object variable
functionalConstr20 arg1 arg2 = mkApp functionalConstr20Symbol [arg1, arg2]

sortToolsMapping :: [(SymbolOrAlias Object, ApplicationSorts Object)]
sortToolsMapping =
    [   ( aSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult = testSort
            }
        )
    ,   ( bSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult = testSort
            }
        )
    ,   ( cSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult = testSort
            }
        )
    ,   ( dSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult = testSort
            }
        )
    ,   ( eSymbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult = testSort
            }
        )
    ,   ( fSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( gSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( hSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( cfSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( cgSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( chSymbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( plain00Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult = testSort
            }
        )
    ,   ( plain10Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( plain20Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort, testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( constr10Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( constr11Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( constr20Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort, testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( functional00Symbol
        , ApplicationSorts
            { applicationSortsOperands = []
            , applicationSortsResult = testSort
            }
        )
    ,   ( functional10Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( functional11Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( functional20Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort, testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( functionalConstr10Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort]
            , applicationSortsResult = testSort
            }
        )
    ,   ( functionalConstr20Symbol
        , ApplicationSorts
            { applicationSortsOperands = [testSort, testSort]
            , applicationSortsResult = testSort
            }
        )
    ]

attributesMapping :: [(SymbolOrAlias Object, StepperAttributes)]
attributesMapping =
    [   ( aSymbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( bSymbol
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
    ,   ( cgSymbol
        , Mock.functionAttributes
        )
    ,   ( chSymbol
        , Mock.functionAttributes
        )
    ,   ( plain00Symbol
        , Mock.defaultAttributes
        )
    ,   ( plain10Symbol
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
    ,   ( functional00Symbol
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
    ,   ( functionalConstr10Symbol
        , Mock.constructorFunctionalAttributes
        )
    ,   ( functionalConstr20Symbol
        , Mock.constructorFunctionalAttributes
        )
    ]

testSort :: Sort Object
testSort =
    SortActualSort SortActual
        { sortActualName  = testId "testSort"
        , sortActualSorts = []
        }
