module Data.Kore.ASTTraversalsTest where

import           Test.Tasty              (TestTree, testGroup)
import           Test.Tasty.HUnit        (assertEqual, testCase)

import           Data.Kore.AST
import           Data.Kore.ASTTraversals


lhs :: UnifiedPattern -> UnifiedPattern
lhs = topDownVisitor leftImplies asUnifiedPattern
  where
    leftImplies (ImpliesPattern ip) = Left (impliesFirst ip)
    leftImplies p                   = Right p

astTraversalsTests :: TestTree
astTraversalsTests =
    testGroup
        "ASTTraversal Tests"
        [ testCase "Testing topDownVisitor"
            (assertEqual ""
                (ObjectPattern $ ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "sigma"
                        , symbolOrAliasParams = []
                        }
                    , applicationChildren =
                        [ MetaPattern $ StringLiteralPattern $
                                StringLiteral "left1"
                        ,  MetaPattern $ StringLiteralPattern $
                                StringLiteral "left2"
                        ]
                    }
                )
                (lhs $ ObjectPattern $ ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "sigma"
                        , symbolOrAliasParams = []
                        }
                    , applicationChildren =
                        [ ObjectPattern $ ImpliesPattern Implies
                            { impliesSort = SortVariableSort $ SortVariable $
                                Id "#a"
                            , impliesFirst = MetaPattern $ StringLiteralPattern
                                (StringLiteral "left1")
                            , impliesSecond = MetaPattern $ StringLiteralPattern
                                (StringLiteral "right1")
                            }
                        ,  ObjectPattern $ ImpliesPattern Implies
                            { impliesSort = SortVariableSort $ SortVariable $
                                Id "#b"
                            , impliesFirst = MetaPattern $ StringLiteralPattern
                                (StringLiteral "left2")
                            , impliesSecond = MetaPattern $ StringLiteralPattern
                                (StringLiteral "right2")
                            }
                        ]
                    }
                )
            )
        ]
