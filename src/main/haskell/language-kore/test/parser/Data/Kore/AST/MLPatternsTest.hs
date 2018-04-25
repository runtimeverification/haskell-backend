{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module  Data.Kore.AST.MLPatternsTest (mlPatternsTests) where

import           Test.Tasty                  (TestTree, testGroup)
import           Test.Tasty.HUnit            (assertEqual, testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore          (UnifiedPattern)
import           Data.Kore.AST.MLPatterns
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts    as Sorts

mlPatternsTests :: TestTree
mlPatternsTests =
    testGroup "Tests for generic pattern handling"
        [applyPatternFunctionTests]

applyPatternFunctionTests :: TestTree
applyPatternFunctionTests =
    testGroup "Tests for applyPatternFunction"
        [ testCase "Applies function on `And`"
            (assertEqual
                "Expecting And's sort"
                (asAst sort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern (metaAnd sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Application`"
            (assertEqual
                "Expecting Application's parameter sort"
                (asAst SortListSort :: Sort Meta)
                (metaFunctionApplier
                    (ApplicationPattern Application
                        { applicationSymbolOrAlias = SymbolOrAlias
                            { symbolOrAliasConstructor = Id "#sigma"
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
                (metaFunctionApplier
                    (asMetaPattern (metaBottom sort))
                )
            )
        , testCase "Applies function on `Ceil`"
            (assertEqual
                "Expecting Ceil's sort"
                (asAst otherSort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern
                        (metaCeil (ResultSort otherSort) sort mVariable)
                    )
                )
            )
        , testCase "Applies function on `DomainValue`"
            (assertEqual
                "Expecting DomainValue's sort"
                (asAst objectSort :: Sort Object)
                (objectFunctionApplier
                    (asObjectPattern
                        (objectDomainValue objectSort (metaString "Something"))
                    )
                )
            )
        , testCase "Applies function on `Equals`"
            (assertEqual
                "Expecting Equals's sort"
                (asAst otherSort :: Sort Meta)
                (metaFunctionApplier
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
                (metaFunctionApplier
                    (asMetaPattern (metaExists sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Floor`"
            (assertEqual
                "Expecting Floor's sort"
                (asAst otherSort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern
                        (metaFloor (ResultSort otherSort) sort mVariable)
                    )
                )
            )
        , testCase "Applies function on `Forall`"
            (assertEqual
                "Expecting Forall's sort"
                (asAst sort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern (metaForall sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Iff`"
            (assertEqual
                "Expecting Iff's sort"
                (asAst sort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern (metaIff sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Implies`"
            (assertEqual
                "Expecting Implies' sort"
                (asAst sort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern (metaImplies sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `In`"
            (assertEqual
                "Expecting In's sort"
                (asAst otherSort :: Sort Meta)
                (metaFunctionApplier
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
                (objectFunctionApplier
                    (asObjectPattern (objectNext objectSort oVariable))
                )
            )
        , testCase "Applies function on `Not`"
            (assertEqual
                "Expecting Not's sort"
                (asAst sort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern (metaNot sort mVariable))
                )
            )
        , testCase "Applies function on `Or`"
            (assertEqual
                "Expecting Or's sort"
                (asAst sort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern (metaOr sort mVariable mVariable))
                )
            )
        , testCase "Applies function on `Rewrites`"
            (assertEqual
                "Expecting Rewrites' sort"
                (asAst objectSort :: Sort Object)
                (objectFunctionApplier
                    (asObjectPattern
                        (objectRewrites objectSort oVariable oVariable)
                    )
                )
            )
        , testCase "Applies function on `Top`"
            (assertEqual
                "Expecting Top's sort"
                (asAst sort :: Sort Meta)
                (metaFunctionApplier
                    (asMetaPattern (metaTop sort))
                )
            )
        ]
  where
    sort = Sorts.CharSort
    otherSort = Sorts.SortSort
    objectSort = SomeObjectSort
    mVariable = metaVariable "#x" sort
    oVariable = objectVariable "x" objectSort

metaFunctionApplier :: Pattern Meta Variable UnifiedPattern -> Sort Meta
metaFunctionApplier =
    applyPatternFunction
        PatternFunction
            { patternFunctionML = getMLPatternResultSort
            , patternFunctionMLBinder = getBinderPatternSort
            , stringFunction = const (asAst CharListSort)
            , charFunction = const (asAst Sorts.CharSort)
            , applicationFunction =
                head . symbolOrAliasParams . applicationSymbolOrAlias
            , variableFunction = variableSort
            }

objectFunctionApplier :: Pattern Object Variable UnifiedPattern -> Sort Object
objectFunctionApplier =
    applyPatternFunction
        PatternFunction
            { patternFunctionML = getMLPatternResultSort
            , patternFunctionMLBinder = getBinderPatternSort
            , stringFunction = undefined
            , charFunction = undefined
            , applicationFunction =
                head . symbolOrAliasParams . applicationSymbolOrAlias
            , variableFunction = variableSort
            }

data SomeObjectSort = SomeObjectSort
instance AsAst (Sort Object) SomeObjectSort where
    asAst _ =
        SortActualSort SortActual
            { sortActualName = Id "SomeObjectSort"
            , sortActualSorts = []
            }


