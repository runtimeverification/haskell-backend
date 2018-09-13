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
                 ( Application (..), AstLocation (..), Id (..), Sort (..),
                 SymbolOrAlias (..), Variable (..), KoreDomain )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
                 ( mkApp, mkBottom )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern Bottom_ )
import           Kore.Error
                 ( printError )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( makeAndPredicate, makeEqualsPredicate, makeFalsePredicate,
                 makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (ApplicationFunctionEvaluator),
                 CommonApplicationFunctionEvaluator )
import qualified Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern, OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Simplification.Application
                 ( simplify )
import           Kore.Step.Simplification.Data
                 ( CommonPureMLPatternSimplifier,
                 evalSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore
                 ( testId )
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
                 ( constructorFunctionalAttributes, functionAttributes,
                 makeMetadataTools, makeSortTools )
import           Test.Kore.Step.Simplifier
                 ( mockSimplifier )
import           Test.Tasty.HUnit.Extensions

test_applicationSimplification :: [TestTree]
test_applicationSimplification =
    [ testCase "Application - or distribution"
        -- sigma(a or b, c or d) =
        --     sigma(b, d) or sigma(b, c) or sigma(a, d) or sigma(a, c)
        (assertEqualWithExplanation ""
            (OrOfExpandedPattern.make
                [ ExpandedPattern
                    { term = give mockSortTools $
                        mkApp sigmaSymbol [a, c]
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = give mockSortTools $
                        mkApp sigmaSymbol [a, d]
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                , ExpandedPattern
                    { term = give mockSortTools $
                        mkApp sigmaSymbol [b, c]
                    , predicate = makeTruePredicate
                    , substitution = []
                    }
                ,  ExpandedPattern
                    { term = give mockSortTools $
                        mkApp sigmaSymbol [b, d]
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
                [ ExpandedPattern
                    { term = mkBottom
                    , predicate = makeFalsePredicate
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
                        (const $ const $ const $ return
                            ( AttemptedFunction.Applied
                                (OrOfExpandedPattern.make [gOfAExpanded])
                            , ()
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
                [ ExpandedPattern
                    { term = give mockSortTools $
                        mkApp sigmaSymbol [a, b]
                    , predicate = fst $ give mockSortTools $ makeAndPredicate
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
                    [   [ ExpandedPattern
                            { term = a
                            , predicate = give mockSortTools $
                                makeEqualsPredicate fOfA fOfB
                            , substitution = [ (x, fOfA) ]
                            }
                        ]
                    ,   [ ExpandedPattern
                            { term = b
                            , predicate = give mockSortTools $
                                makeEqualsPredicate gOfA gOfB
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
                [ ExpandedPattern
                    { term = give mockSortTools $
                        mkApp fSymbol [a]
                    , predicate =
                        fst $ give mockSortTools $ makeAndPredicate
                            (makeEqualsPredicate fOfA gOfA)
                            (fst $ makeAndPredicate
                                (makeEqualsPredicate fOfA fOfB)
                                (makeEqualsPredicate gOfA gOfB)
                            )
                    , substitution =
                        [ (x, fOfA)
                        , (y, gOfA)
                        , (z, gOfB)
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
                        (const $ const $ const $ return
                            ( AttemptedFunction.Applied
                                (OrOfExpandedPattern.make
                                    [ ExpandedPattern
                                        { term = give mockSortTools $
                                            mkApp fSymbol [a]
                                        , predicate =
                                            give mockSortTools $
                                                makeEqualsPredicate fOfA gOfA
                                        , substitution =
                                            [ (z, gOfB) ]
                                        }
                                    ]
                                )
                            , ()
                            )
                        )
                    ]
                )
                (makeApplication
                    sigmaSymbol
                    [   [ ExpandedPattern
                            { term = a
                            , predicate = give mockSortTools $
                                makeEqualsPredicate fOfA fOfB
                            , substitution = [ (x, fOfA) ]
                            }
                        ]
                    ,   [ ExpandedPattern
                            { term = b
                            , predicate = give mockSortTools $
                                makeEqualsPredicate gOfA gOfB
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
    a, b, c, d, fOfA, fOfB, gOfA, gOfB :: PureMLPattern Object KoreDomain Variable
    a = give mockSortTools $ mkApp aSymbol []
    b = give mockSortTools $ mkApp bSymbol []
    c = give mockSortTools $ mkApp cSymbol []
    d = give mockSortTools $ mkApp dSymbol []
    fOfA = give mockSortTools $ mkApp fSymbol [a]
    fOfB = give mockSortTools $ mkApp fSymbol [b]
    gOfA = give mockSortTools $ mkApp gSymbol [a]
    gOfB = give mockSortTools $ mkApp gSymbol [b]
    aExpanded = ExpandedPattern
        { term = a
        , predicate = makeTruePredicate
        , substitution = []
        }
    bExpanded = ExpandedPattern
        { term = b
        , predicate = makeTruePredicate
        , substitution = []
        }
    cExpanded = ExpandedPattern
        { term = c
        , predicate = makeTruePredicate
        , substitution = []
        }
    dExpanded = ExpandedPattern
        { term = d
        , predicate = makeTruePredicate
        , substitution = []
        }
    gOfAExpanded = ExpandedPattern
        { term = gOfA
        , predicate = makeTruePredicate
        , substitution = []
        }
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
    mockSortTools = Mock.makeSortTools sortToolsMapping
    mockMetadataTools = Mock.makeMetadataTools mockSortTools attributesMapping

makeApplication
    :: SymbolOrAlias level
    -> [[ExpandedPattern level domain variable]]
    -> Application level (OrOfExpandedPattern level domain variable)
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
    -> CommonPureMLPatternSimplifier level KoreDomain
    -- ^ Evaluates functions.
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level KoreDomain]
    -- ^ Map from symbol IDs to defined functions
    -> Application level (CommonOrOfExpandedPattern level KoreDomain)
    -> CommonOrOfExpandedPattern level KoreDomain
evaluate
    tools
    simplifier
    symbolIdToEvaluator
    application
  =
    either (error . printError) fst
        $ evalSimplifier
        $ simplify tools simplifier symbolIdToEvaluator application
