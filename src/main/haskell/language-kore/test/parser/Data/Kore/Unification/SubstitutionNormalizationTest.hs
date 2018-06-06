{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Data.Kore.Unification.SubstitutionNormalizationTest
    (substitutionNormalizationTests)
  where

import           Test.Tasty                                      (TestTree,
                                                                  testGroup)
import           Test.Tasty.HUnit                                (assertEqual,
                                                                  testCase)

import           Data.Kore.AST.Common                            (AstLocation (..),
                                                                  Variable)
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML                            (CommonPurePattern)
import           Data.Kore.AST.PureToKore                        (patternKoreToPure)
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts
import           Data.Kore.MetaML.AST                            (CommonMetaPattern)
import           Data.Kore.Unification.Error                     (SubstitutionError (..),
                                                                  UnificationError (..))
import           Data.Kore.Unification.SubstitutionNormalization
import           Data.Kore.Unification.UnifierImpl               (UnificationSubstitution)
import           Data.Kore.Variables.Fresh.IntCounter            (runIntCounter)

substitutionNormalizationTests :: TestTree
substitutionNormalizationTests =
    testGroup
        "Substitution normalization test"
        [ testCase "Empty substitution"
            (assertEqual ""
                (Right [])
                (runNormalizeSubstitution
                    ([] :: [(Variable Meta, CommonPurePattern Meta)])
                )
            )
        , testCase "Simple substitution"
            (assertEqual ""
                (Right
                    [   ( asVariable (v1 PatternSort)
                        , asPureMetaPattern (metaTop PatternSort)
                        )
                    ]
                )
                (runNormalizeSubstitution
                    [   ( asVariable (v1 PatternSort)
                        , asPureMetaPattern (metaTop PatternSort)
                        )
                    ]
                )
            )
        , testCase "Simple unnormalized substitution"
            (assertEqual ""
                (Right
                    [   ( asVariable (v1 PatternSort)
                        , asPureMetaPattern (metaTop PatternSort)
                        )
                    ,   ( asVariable (x1 PatternSort)
                        , asPureMetaPattern (metaTop PatternSort)
                        )
                    ]
                )
                (runNormalizeSubstitution
                    [   ( asVariable (v1 PatternSort)
                        , asPureMetaPattern (x1 PatternSort)
                        )
                    ,   ( asVariable (x1 PatternSort)
                        , asPureMetaPattern (metaTop PatternSort)
                        )
                    ]
                )
            )
        , testCase "Unnormalized substitution with 'and'"
            (assertEqual ""
                (Right
                    [   ( asVariable (v1 PatternSort)
                        , asPureMetaPattern
                            ( metaAnd
                                PatternSort
                                (metaTop PatternSort)
                                (metaTop PatternSort)
                            )
                        )
                    ,   ( asVariable (x1 PatternSort)
                        , asPureMetaPattern (metaTop PatternSort)
                        )
                    ]
                )
                (runNormalizeSubstitution
                    [   ( asVariable (v1 PatternSort)
                        , asPureMetaPattern
                            ( metaAnd
                                PatternSort
                                (x1 PatternSort)
                                (metaTop PatternSort)
                            )
                        )
                    ,   ( asVariable (x1 PatternSort)
                        , asPureMetaPattern (metaTop PatternSort)
                        )
                    ]
                )
            )
        , let
            var1 = asVariable (v1 PatternSort)
          in
            testCase "Simplest cycle"
                (assertEqual ""
                    (Left (CircularVariableDependency [var1]))
                    (runNormalizeSubstitution
                        [   ( var1
                            , asPureMetaPattern (v1 PatternSort)
                            )
                        ]
                    )
                )
        , let
            var1 = asVariable (v1 PatternSort)
            varx1 = asVariable (x1 PatternSort)
          in
            testCase "Length 2 cycle"
                (assertEqual ""
                    (Left (CircularVariableDependency [var1, varx1]))
                    (runNormalizeSubstitution
                        [   ( var1
                            , asPureMetaPattern (x1 PatternSort)
                            )
                        ,   ( varx1
                            , asPureMetaPattern (v1 PatternSort)
                            )
                        ]
                    )
                )
        , let
            var1 = asVariable (v1 PatternSort)
            varx1 = asVariable (x1 PatternSort)
          in
            testCase "Cycle with 'and'"
                (assertEqual ""
                    (Left (CircularVariableDependency [var1, varx1]))
                    (runNormalizeSubstitution
                        [   ( var1
                            , asPureMetaPattern
                                ( metaAnd
                                    PatternSort
                                    (x1 PatternSort)
                                    (metaTop PatternSort)
                                )
                            )
                        ,   ( varx1
                            , asPureMetaPattern
                                ( metaAnd
                                    PatternSort
                                    (v1 PatternSort)
                                    (metaTop PatternSort)
                                )
                            )
                        ]
                    )
                )
        ]
  where
    v1 :: MetaSort sort => sort -> MetaVariable sort
    v1 = metaVariable "v1" AstLocationTest
    x1 :: MetaSort sort => sort -> MetaVariable sort
    x1 = metaVariable "x1" AstLocationTest
    asPureMetaPattern
        :: ProperPattern level sort patt => patt -> CommonMetaPattern
    asPureMetaPattern patt = patternKoreToPure Meta (asAst patt)

runNormalizeSubstitution
    :: MetaOrObject level
    => UnificationSubstitution level Variable
    -> Either
        (SubstitutionError level Variable)
        (UnificationSubstitution level Variable)
runNormalizeSubstitution substitution =
    case normalizeSubstitution substitution of
        Left err     -> Left err
        Right action -> Right $ fst $ runIntCounter action 0
