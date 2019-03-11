module Test.Kore.Attribute.Subsort where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Kore
import Kore.Attribute.Subsort

import Test.Kore
       ( sortActual )
import Test.Kore.Attribute.Parser

sub :: Sort Object
sub = sortActual "sub" []

super :: Sort Object
super = sortActual "super" []

parseSubsorts :: Attributes -> Parser Subsorts
parseSubsorts = parseAttributes

test_subsort :: TestTree
test_subsort =
    testCase "[subsort{sub{},super{}}()] :: Subsort"
        $ expectSuccess subsorts
        $ parseSubsorts $ Attributes [ subsortAttribute sub super ]
  where
    subsorts =
        Subsorts
            { getSubsorts =
                [ Subsort { subsort = sub , supersort = super } ]
            }

test_Attributes :: TestTree
test_Attributes =
    testCase "[subsort{sub{},super{}}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ subsortAttribute sub super ]

test_zeroParams :: TestTree
test_zeroParams =
    testCase "[subsort{}()]"
        $ expectFailure
        $ parseSubsorts $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = subsortId
                        , symbolOrAliasParams = []
                        }
                , applicationChildren = []
                }

test_arguments :: TestTree
test_arguments =
    testCase "[subsort{sub{},super{}}(illegal)]"
        $ expectFailure
        $ parseSubsorts $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = subsortSymbol sub super
                , applicationChildren =
                    [ (asCommonKorePattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }
