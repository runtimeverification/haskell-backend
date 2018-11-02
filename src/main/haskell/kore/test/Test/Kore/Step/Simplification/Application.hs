module Test.Kore.Step.Simplification.Application
    ( test_applicationSimplification
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import qualified Data.Map as Map
import           Data.Reflection
                 ( give )

import           Kore.AST.Common
                 ( Application (..), AstLocation (..), Id (..), PureMLPattern,
                 Sort (..), SymbolOrAlias (..), Variable (..) )
import           Kore.AST.MetaOrObject
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkApp, mkBottom )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (ApplicationFunctionEvaluator) )
import qualified Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Application
                 ( simplify )
import           Kore.Step.Simplification.Data
                 ( CommonPureMLPatternSimplifier, SimplificationProof (..),
                 evalSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Variables.Fresh
                 ( freshVariableFromVariable )

import           Test.Kore
                 ( testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( constructorFunctionalAttributes, functionAttributes,
                 makeMetadataTools, makeSymbolOrAliasSorts )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.Kore.Step.Simplifier
                 ( mockSimplifier )
import           Test.Tasty.HUnit.Extensions

test_applicationSimplification :: [TestTree]
test_applicationSimplification = give mockSymbolOrAliasSorts
    [ testCase "Application - or distribution"
        -- sigma(a or b, c or d) =
        --     sigma(b, d) or sigma(b, c) or sigma(a, d) or sigma(a, c)
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkApp sigmaSymbol [a, c]
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Predicated
                    { term = mkApp sigmaSymbol [a, d]
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , Predicated
                    { term = mkApp sigmaSymbol [b, c]
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ,  Predicated
                    { term = mkApp sigmaSymbol [b, d]
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                (mockSimplifier [])
                Map.empty
                (makeApplication
                    sigmaSymbol
                    [ [aExpanded, bExpanded]
                    , [cExpanded, dExpanded]
                    ]
                )
            )
        )
    , testCase "Application - bottom child makes everything bottom"
        -- sigma(a or b, bottom) = bottom
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern.bottom ]
            )
            (evaluate
                mockMetadataTools
                (mockSimplifier [])
                Map.empty
                (makeApplication
                    sigmaSymbol
                    [ [aExpanded, bExpanded]
                    , []
                    ]
                )
            )
        )
    , testCase "Applies functions"
        -- f(a) evaluated to g(a).
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ gOfAExpanded ]
            )
            (evaluate
                mockMetadataTools
                (mockSimplifier [])
                (Map.singleton
                    fId
                    [ ApplicationFunctionEvaluator
                        (const $ const $ const $ const $ return
                            ( AttemptedFunction.Applied
                                (OrOfExpandedPattern.make [gOfAExpanded])
                            , SimplificationProof
                            )
                        )
                    ]
                )
                (makeApplication
                    fSymbol
                    [[aExpanded]]
                )
            )
        )
    , testCase
        "Combines child predicates and substitutions when not aplying functions"
        -- sigma(a and f(a)=f(b) and [x=f(a)], b and g(a)=g(b) and [y=g(a)])
        --    = sigma(a, b) and (f(a)=f(b) and g(a)=g(b)) and [x=f(a), y=g(a)]
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkApp sigmaSymbol [a, b]
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA fOfB)
                            (makeEqualsPredicate gOfA gOfB)
                    , substitution =
                        [ (x, fOfA)
                        , (y, gOfA)
                        ]
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                (mockSimplifier [])
                Map.empty
                (makeApplication
                    sigmaSymbol
                    [   [ Predicated
                            { term = a
                            , predicate = makeEqualsPredicate fOfA fOfB
                            , substitution = [ (x, fOfA) ]
                            }
                        ]
                    ,   [ Predicated
                            { term = b
                            , predicate = makeEqualsPredicate gOfA gOfB
                            , substitution = [ (y, gOfA) ]
                            }
                        ]
                    ]
                )
            )
        )
    , testCase
        "Combines child predicates and substitutions when aplying functions"
        -- sigma(a and f(a)=f(b) and [x=f(a)], b and g(a)=g(b) and [y=g(a)])
        --    =
        --        f(a) and
        --        (f(a)=f(b) and g(a)=g(b) and f(a)=g(a)) and
        --        [x=f(a), y=g(a), z=f(b)]
        -- if sigma(a, b) => f(a) and f(a)=g(a) and [z=f(b)]
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ Predicated
                    { term = mkApp fSymbol [a]
                    , predicate =
                        makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (makeAndPredicate
                                (makeEqualsPredicate fOfA fOfB)
                                (makeEqualsPredicate gOfA gOfB)
                            )
                    , substitution =
                        [ (freshVariableFromVariable z 1, gOfB)
                        , (x, fOfA)
                        , (y, gOfA)
                        ]
                    }
                ]
            )
            (evaluate
                mockMetadataTools
                (mockSimplifier [])
                (Map.singleton
                    sigmaId
                    [ ApplicationFunctionEvaluator
                        (const $ const $ const $ const $ do
                            let zvar = freshVariableFromVariable z 1
                            return
                                ( AttemptedFunction.Applied
                                    (OrOfExpandedPattern.make
                                        [ Predicated
                                            { term = mkApp fSymbol [a]
                                            , predicate =
                                                makeEqualsPredicate fOfA gOfA
                                            , substitution =
                                                [ (zvar, gOfB) ]
                                            }
                                        ]
                                    )
                                , SimplificationProof
                                )
                        )
                    ]
                )
                (makeApplication
                    sigmaSymbol
                    [   [ Predicated
                            { term = a
                            , predicate = makeEqualsPredicate fOfA fOfB
                            , substitution = [ (x, fOfA) ]
                            }
                        ]
                    ,   [ Predicated
                            { term = b
                            , predicate = makeEqualsPredicate gOfA gOfB
                            , substitution = [ (y, gOfA) ]
                            }
                        ]
                    ]
                )
            )
        )
    ]
  where
    fId = Id "f" AstLocationTest
    gId = Id "g" AstLocationTest
    sigmaId = Id "sigma" AstLocationTest
    aSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = Id "a" AstLocationTest
        , symbolOrAliasParams      = []
        }
    bSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = Id "b" AstLocationTest
        , symbolOrAliasParams      = []
        }
    cSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = Id "c" AstLocationTest
        , symbolOrAliasParams      = []
        }
    dSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = Id "d" AstLocationTest
        , symbolOrAliasParams      = []
        }
    fSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = fId
        , symbolOrAliasParams      = []
        }
    gSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = gId
        , symbolOrAliasParams      = []
        }
    sigmaSymbol = SymbolOrAlias
        { symbolOrAliasConstructor = sigmaId
        , symbolOrAliasParams      = []
        }
    x = Variable (testId "x") testSort
    y = Variable (testId "y") testSort
    z = Variable (testId "z") testSort

    a = give mockSymbolOrAliasSorts $ mkApp aSymbol []
    b = give mockSymbolOrAliasSorts $ mkApp bSymbol []
    c = give mockSymbolOrAliasSorts $ mkApp cSymbol []
    d = give mockSymbolOrAliasSorts $ mkApp dSymbol []
    fOfA :: PureMLPattern Object variable
    fOfA = give mockSymbolOrAliasSorts $ mkApp fSymbol [a]
    fOfB = give mockSymbolOrAliasSorts $ mkApp fSymbol [b]
    gOfA :: PureMLPattern Object variable
    gOfA = give mockSymbolOrAliasSorts $ mkApp gSymbol [a]
    gOfB :: PureMLPattern Object variable
    gOfB = give mockSymbolOrAliasSorts $ mkApp gSymbol [b]
    aExpanded = Predicated
        { term = a
        , predicate = makeTruePredicate
        , substitution = []
        }
    bExpanded = Predicated
        { term = b
        , predicate = makeTruePredicate
        , substitution = []
        }
    cExpanded = Predicated
        { term = c
        , predicate = makeTruePredicate
        , substitution = []
        }
    dExpanded = Predicated
        { term = d
        , predicate = makeTruePredicate
        , substitution = []
        }
    gOfAExpanded :: ExpandedPattern Object variable
    gOfAExpanded = Predicated
        { term = gOfA
        , predicate = makeTruePredicate
        , substitution = []
        }
    symbolOrAliasSortsMapping =
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
        ,   ( sigmaSymbol
            , ApplicationSorts
                { applicationSortsOperands = [testSort, testSort]
                , applicationSortsResult = testSort
                }
            )
        ]
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
        ,   ( fSymbol
            , Mock.functionAttributes
            )
        ,   ( gSymbol
            , Mock.functionAttributes
            )
        ,   ( sigmaSymbol
            , Mock.constructorFunctionalAttributes
            )
        ]
    headTypeMapping =
        [   ( aSymbol
            , HeadType.Symbol
            )
        ,   ( bSymbol
            , HeadType.Symbol
            )
        ,   ( cSymbol
            , HeadType.Symbol
            )
        ,   ( dSymbol
            , HeadType.Symbol
            )
        ,   ( fSymbol
            , HeadType.Symbol
            )
        ,   ( gSymbol
            , HeadType.Symbol
            )
        ,   ( sigmaSymbol
            , HeadType.Symbol
            )
        ]
    mockSymbolOrAliasSorts =
        Mock.makeSymbolOrAliasSorts symbolOrAliasSortsMapping
    mockMetadataTools =
        Mock.makeMetadataTools
            mockSymbolOrAliasSorts attributesMapping headTypeMapping []

makeApplication
    :: (MetaOrObject level, Ord (variable level))
    => SymbolOrAlias level
    -> [[ExpandedPattern level variable]]
    -> Application level (OrOfExpandedPattern level variable)
makeApplication symbol patterns =
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = map OrOfExpandedPattern.make patterns
        }

testSort :: Sort Object
testSort =
    case mkBottom of
        Bottom_ sort -> sort
        _ -> error "unexpected"

evaluate
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> CommonPureMLPatternSimplifier level
    -- ^ Evaluates functions.
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -- ^ Map from symbol IDs to defined functions
    -> Application level (CommonOrOfExpandedPattern level)
    -> CommonOrOfExpandedPattern level
evaluate
    tools
    simplifier
    symbolIdToEvaluator
    application
  =
    fst
        $ evalSimplifier
        $ simplify
            tools
            (Mock.substitutionSimplifier tools)
            simplifier
            symbolIdToEvaluator
            application
