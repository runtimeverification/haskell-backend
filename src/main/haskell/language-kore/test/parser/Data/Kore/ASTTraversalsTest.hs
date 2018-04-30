module Data.Kore.ASTTraversalsTest where

import           Test.Tasty                 (TestTree, testGroup)
import           Test.Tasty.HUnit           (assertEqual, testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.ASTTraversals


lhs :: CommonKorePattern -> CommonKorePattern
lhs = koreTopDownVisitor leftImplies asKorePattern
  where
    leftImplies (ImpliesPattern ip) = Left (impliesFirst ip)
    leftImplies p                   = Right p

astTraversalsTests :: TestTree
astTraversalsTests =
    testGroup
        "ASTTraversal Tests"
        [ testCase "Testing topDownVisitor"
            (assertEqual ""
                (asKorePattern $ ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "sigma"
                        , symbolOrAliasParams = []
                        } :: SymbolOrAlias Object
                    , applicationChildren =
                        [ asKorePattern $ StringLiteralPattern $
                                StringLiteral "left1"
                        ,  asKorePattern $ StringLiteralPattern $
                                StringLiteral "left2"
                        ]
                    }
                )
                (lhs $ asKorePattern $ ApplicationPattern Application
                    { applicationSymbolOrAlias = SymbolOrAlias
                        { symbolOrAliasConstructor = Id "sigma"
                        , symbolOrAliasParams = []
                        } :: SymbolOrAlias Object
                    , applicationChildren =
                        [ asKorePattern $ ImpliesPattern Implies
                            { impliesSort = SortVariableSort $ SortVariable $
                                Id "#a" :: Sort Meta
                            , impliesFirst = asKorePattern $ StringLiteralPattern
                                (StringLiteral "left1")
                            , impliesSecond = asKorePattern $ StringLiteralPattern
                                (StringLiteral "right1")
                            }
                        ,  asKorePattern $ ImpliesPattern Implies
                            { impliesSort = SortVariableSort $ SortVariable $
                                Id "#b" :: Sort Meta
                            , impliesFirst = asKorePattern $ StringLiteralPattern
                                (StringLiteral "left2")
                            , impliesSecond = asKorePattern $ StringLiteralPattern
                                (StringLiteral "right2")
                            }
                        ]
                    }
                )
            )
        ]
