module Data.Kore.ASTTraversalsTest where

import           Test.Tasty              (TestTree, testGroup)
import           Test.Tasty.HUnit        (assertEqual, testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.ASTTraversals


lhs :: KorePattern -> KorePattern
lhs = topDownVisitor leftImplies asKorePattern
  where
    leftImplies (ImpliesPattern ip) = Left (impliesFirst ip)
    leftImplies p                   = Right p

astTraversalsTests :: TestTree
astTraversalsTests =
    testGroup
        "ASTTraversal Tests"
        [ testCase "Testing topDownVisitor"
            (assertEqual ""
                (asObjectPattern $ ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "sigma"
                        , symbolOrAliasParams = []
                        }
                    , applicationChildren =
                        [ asMetaPattern $ StringLiteralPattern $
                                StringLiteral "left1"
                        ,  asMetaPattern $ StringLiteralPattern $
                                StringLiteral "left2"
                        ]
                    }
                )
                (lhs $ asObjectPattern $ ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "sigma"
                        , symbolOrAliasParams = []
                        }
                    , applicationChildren =
                        [ asObjectPattern $ ImpliesPattern Implies
                            { impliesSort = SortVariableSort $ SortVariable $
                                Id "#a"
                            , impliesFirst = asMetaPattern $ StringLiteralPattern
                                (StringLiteral "left1")
                            , impliesSecond = asMetaPattern $ StringLiteralPattern
                                (StringLiteral "right1")
                            }
                        ,  asObjectPattern $ ImpliesPattern Implies
                            { impliesSort = SortVariableSort $ SortVariable $
                                Id "#b"
                            , impliesFirst = asMetaPattern $ StringLiteralPattern
                                (StringLiteral "left2")
                            , impliesSecond = asMetaPattern $ StringLiteralPattern
                                (StringLiteral "right2")
                            }
                        ]
                    }
                )
            )
        ]
