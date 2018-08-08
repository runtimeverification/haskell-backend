module Test.Kore.ASTTraversals (test_astTraversals) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Control.Monad.Identity

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.ASTTraversals

import Test.Kore


lhs :: CommonKorePattern -> CommonKorePattern
lhs = patternBottomUpVisitor leftImplies
  where
    leftImplies (ImpliesPattern ip) = impliesFirst ip
    leftImplies p                   = asKorePattern p

test_astTraversals :: [TestTree]
test_astTraversals =
    [ testCase "Testing patternBottomUpVisitor"
        (assertEqual ""
            samplePatternExpected
            (lhs samplePattern)
        )
    ]
  where
    samplePatternExpected =
        asKorePattern $ ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId "sigma"
                , symbolOrAliasParams = []
                } :: SymbolOrAlias Object
            , applicationChildren =
                [ asKorePattern $ StringLiteralPattern $ StringLiteral "left1"
                ,  asKorePattern $ StringLiteralPattern $ StringLiteral "left2"
                ]
            }
    samplePattern =
        asKorePattern $ ApplicationPattern Application
            { applicationSymbolOrAlias = SymbolOrAlias
                { symbolOrAliasConstructor = testId "sigma"
                , symbolOrAliasParams = []
                } :: SymbolOrAlias Object
            , applicationChildren =
                [ asKorePattern $ ImpliesPattern Implies
                    { impliesSort = SortVariableSort $ SortVariable $
                        testId "#a" :: Sort Meta
                    , impliesFirst = asKorePattern $ StringLiteralPattern
                        (StringLiteral "left1")
                    , impliesSecond = asKorePattern $ StringLiteralPattern
                        (StringLiteral "right1")
                    }
                ,  asKorePattern $ ImpliesPattern Implies
                    { impliesSort = SortVariableSort $ SortVariable $
                        testId "#b" :: Sort Meta
                    , impliesFirst = asKorePattern $ StringLiteralPattern
                        (StringLiteral "left2")
                    , impliesSecond = asKorePattern $ StringLiteralPattern
                        (StringLiteral "right2")
                    }
                ]
            }

