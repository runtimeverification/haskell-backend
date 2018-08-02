module Test.Kore.AST.MLPatterns
    ( test_mlPattern
    , extractPurePattern
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Data.Functor.Foldable

import Kore.AST.AstWithLocation
import Kore.AST.Builders
import Kore.AST.Common
import Kore.AST.Kore
       ( CommonKorePattern )
import Kore.AST.MetaOrObject
import Kore.AST.MLPatterns
import Kore.AST.PureML
import Kore.AST.Sentence
import Kore.ASTHelpers
       ( ApplicationSorts (..) )
import Kore.Building.AsAst
import Kore.Building.Patterns
import Kore.Building.Sorts as Sorts
import Kore.Implicit.ImplicitSorts

import Test.Kore

extractPurePattern
    :: MetaOrObject level
    => CommonPurePatternStub level -> CommonPurePattern level
extractPurePattern (SortedPatternStub sp) =
    asPurePattern $ sortedPatternPattern sp
extractPurePattern (UnsortedPatternStub ups) =
    error ("Cannot find a sort for "
        ++ show (ups (dummySort (undefined :: level))))

test_mlPattern :: [TestTree]
test_mlPattern =
    [ testGroup "Tests for generic pattern handling"
        [applyPatternFunctionTests]
    , testGroup "Tests for getPatternResultSort"
        [ testCase "MLPatternClas"
            (assertEqual ""
                charListMetaSort
                (getPatternResultSort
                    undefinedHeadSort
                    (project
                      $ extractPurePattern
                        (withSort charListMetaSort top_)
                    )
                )
            )
        , testCase "MLBinderPatternClas"
            (assertEqual ""
                charListMetaSort
                (getPatternResultSort
                    undefinedHeadSort
                    (project
                      $ extractPurePattern
                        (withSort charListMetaSort
                            (forall_
                                (Variable
                                    (testId "x")
                                    charListMetaSort
                                )
                                top_
                            )
                        )
                    )
                )
            )
        , testCase "DomainValue"
        (assertEqual ""
            (asAst SomeObjectSort :: Sort Object)
            (getPatternResultSort
                undefinedHeadSort
                (asObjectPattern
                    (objectDomainValue SomeObjectSort (metaString "Something"))
                )
            )
        )
        , testCase "StringLiteral"
            (assertEqual ""
                charListMetaSort
                (getPatternResultSort
                    undefinedHeadSort
                    (StringLiteralPattern (StringLiteral "Hello!")
                    :: UnFixedPureMLPattern Meta Variable
                    )
                )
            )
        , testCase "CharLiteral"
            (assertEqual ""
                charMetaSort
                (getPatternResultSort
                    undefinedHeadSort
                    (CharLiteralPattern (CharLiteral 'h')
                    :: UnFixedPureMLPattern Meta Variable
                    )
                )
            )
        , testCase "Variable"
            (assertEqual ""
                charListMetaSort
                (getPatternResultSort
                    undefinedHeadSort
                    (VariablePattern (Variable (testId "x") charListMetaSort))
                )
            )
        , let
            s = symbol_ "test" AstLocationTest [] charListMetaSort
            headSort x
                | x == getSentenceSymbolOrAliasHead s [] =
                    ApplicationSorts [] charListMetaSort
                | otherwise =
                    ApplicationSorts [] charMetaSort
            in
            testCase "Application"
                (assertEqual ""
                    charListMetaSort
                    (getPatternResultSort
                        headSort
                        (project $ extractPurePattern (applyS s []))
                    )
                )
            ]
    ]

applyPatternFunctionTests :: TestTree
applyPatternFunctionTests =
    testGroup "Tests for applyPatternFunction"
        [ testCase "Applies function on `And`"
            (assertEqual
                "Expecting And's sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaAnd sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Application`"
            (assertEqual
                "Expecting Application's parameter sort"
                (asAst SortListSort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (ApplicationPattern Application
                        { applicationSymbolOrAlias = SymbolOrAlias
                            { symbolOrAliasConstructor = testId "#sigma"
                            , symbolOrAliasParams = [asAst SortListSort]
                            }
                        , applicationChildren = []
                        }
                    )
                )
            )
        , testCase "Applies function on `Bottom`"
            (assertEqual
                "Expecting Bottom's sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaBottom sort))
                )
            )
        , testCase "Applies function on `Ceil`"
            (assertEqual
                "Expecting Ceil's sort"
                (asAst otherSort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern
                        (metaCeil (ResultSort otherSort) sort mVariable)
                    )
                )
            )
        , testCase "Applies function on `DomainValue`"
            (assertEqual
                "Expecting DomainValue's sort"
                (asAst objectSort :: Sort Object)
                (metaLeveledFunctionApplier
                    (asObjectPattern
                        (objectDomainValue objectSort (metaString "Something"))
                    )
                )
            )
        , testCase "Applies locationFromAst on `DomainValue`"
            (assertEqual
                "Expecting DomainValue's location"
                AstLocationTest
                (locationFromAst
                    (asObjectPattern
                        (objectDomainValue objectSort (metaString "Something"))
                    )
                )
            )
        , testCase "Applies function on `Equals`"
            (assertEqual
                "Expecting Equals's sort"
                (asAst otherSort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern
                        (metaEquals
                            (ResultSort otherSort) sort mVariable mVariable
                        )
                    )
                )
            )
        , testCase "Applies function on `Exists`"
            (assertEqual
                "Expecting Exists's sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaExists sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Floor`"
            (assertEqual
                "Expecting Floor's sort"
                (asAst otherSort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern
                        (metaFloor (ResultSort otherSort) sort mVariable)
                    )
                )
            )
        , testCase "Applies function on `Forall`"
            (assertEqual
                "Expecting Forall's sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaForall sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Iff`"
            (assertEqual
                "Expecting Iff's sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaIff sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Implies`"
            (assertEqual
                "Expecting Implies' sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaImplies sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `In`"
            (assertEqual
                "Expecting In's sort"
                (asAst otherSort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern
                        (metaIn
                            (ResultSort otherSort)
                            sort
                            (ContainedChild mVariable)
                            mVariable)
                    )
                )
            )
        , testCase "Applies function on `Next`"
            (assertEqual
                "Expecting Next's sort"
                (asAst objectSort :: Sort Object)
                (metaLeveledFunctionApplier
                    (asObjectPattern (objectNext objectSort oVariable))
                )
            )
        , testCase "Applies function on `Not`"
            (assertEqual
                "Expecting Not's sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaNot sort mVariable))
                )
            )
        , testCase "Applies function on `Or`"
            (assertEqual
                "Expecting Or's sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaOr sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Rewrites`"
            (assertEqual
                "Expecting Rewrites' sort"
                (asAst objectSort :: Sort Object)
                (metaLeveledFunctionApplier
                    (asObjectPattern
                        (objectRewrites objectSort oVariable oVariable)
                    )
                )
            )
        , testCase "Applies function on `Top`"
            (assertEqual
                "Expecting Top's sort"
                (asAst sort :: Sort Meta)
                (metaLeveledFunctionApplier
                    (asMetaPattern (metaTop sort))
                )
            )
        ]
  where
    sort = Sorts.CharSort
    otherSort = Sorts.SortSort
    objectSort = SomeObjectSort
    mVariable = metaVariable "#x" AstLocationTest sort
    oVariable = objectVariable "x" AstLocationTest objectSort

metaLeveledFunctionApplier :: Pattern level Variable CommonKorePattern -> Sort level
metaLeveledFunctionApplier =
    applyPatternLeveledFunction
        PatternLeveledFunction
            { patternLeveledFunctionML = getMLPatternResultSort
            , patternLeveledFunctionMLBinder = getBinderPatternSort
            , stringLeveledFunction = const (asAst CharListSort)
            , charLeveledFunction = const (asAst Sorts.CharSort)
            , applicationLeveledFunction =
                head . symbolOrAliasParams . applicationSymbolOrAlias
            , variableLeveledFunction = variableSort
            , domainValueLeveledFunction = domainValueSort
            }

data SomeObjectSort = SomeObjectSort
instance AsAst (Sort Object) SomeObjectSort where
    asAst _ =
        SortActualSort SortActual
            { sortActualName = testId "SomeObjectSort"
            , sortActualSorts = []
            }


