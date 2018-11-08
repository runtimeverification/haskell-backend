module Test.Kore.Attribute.Parser where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Default
       ( Default )
import Data.Either
       ( isLeft )

import qualified Kore.AST.Common as Kore
import qualified Kore.AST.Kore as Kore
import           Kore.AST.Sentence
                 ( Attributes (..) )
import qualified Kore.AST.Sentence as Kore
import qualified Kore.ASTUtils.SmartPatterns as Kore
import           Kore.Attribute.Hook
                 ( Hook (..) )
import qualified Kore.Attribute.Hook as Hook
import           Kore.Attribute.Parser
import           Kore.Error
                 ( Error )

-- | Demonstrate that two parsers are equivalent under the same attributes.
equiv
    :: (Default a, Eq a, Show a)
    => (Attributes -> Parser a)
    -> (Attributes -> Parser a)
    -> Attributes
    -> Assertion
equiv expected actual attrs =
    expected attrs @=? actual attrs

emptyAttrs :: Kore.Attributes
emptyAttrs = Kore.Attributes []

test_parseAttributes :: [TestTree]
test_parseAttributes =
    [   let
            expect = return
            actual = parseAttributes
            attrs = multipleAttrs
        in
            testCase "Reconstructs parsed attributes"
                (equiv expect actual attrs)
    ]

key :: Kore.CommonKorePattern
key =
    (Kore.KoreObjectPattern . Kore.ApplicationPattern)
        Kore.Application
            { applicationSymbolOrAlias =
                Kore.SymbolOrAlias
                    { symbolOrAliasConstructor = "key"
                    , symbolOrAliasParams = []
                    }
            , applicationChildren = []
            }

keyAttrs :: Kore.Attributes
keyAttrs = Kore.Attributes [ key ]

multipleAttrs :: Kore.Attributes
multipleAttrs = Kore.Attributes [ key, key ]

dv :: Kore.CommonKorePattern
dv =
    (Kore.asKorePattern . Kore.DomainValuePattern)
        Kore.DomainValue
            { domainValueSort =
                Kore.SortActualSort Kore.SortActual
                    { sortActualName =
                        Kore.Id
                            { getId = "Bool"
                            , idLocation = Kore.AstLocationTest
                            }
                    , sortActualSorts = []
                    }
            , domainValueChild =
                Kore.BuiltinDomainPattern (Kore.StringLiteral_ "true")
            }

dvAttrs :: Kore.Attributes
dvAttrs = Kore.Attributes [ dv ]

char :: Kore.CommonKorePattern
char = (Kore.asKorePattern . Kore.CharLiteralPattern) (Kore.CharLiteral 'A')

charAttrs :: Kore.Attributes
charAttrs = Kore.Attributes [ char ]

charHook :: Kore.Attributes
charHook =
    Kore.Attributes
        [ (Kore.asKorePattern . Kore.ApplicationPattern)
              Kore.Application
                  { applicationSymbolOrAlias = Hook.hookSymbol
                  , applicationChildren = [char]
                  }
        ]

test_parseAttributes_Hook :: [TestTree]
test_parseAttributes_Hook =
    [ testCase "Rejects literal character arguments"
        $ assertBool "expected error" $ isLeft $ actual charHook
    , testCase "Rejects object-level arguments"
        $ assertBool "expected error" $ isLeft $ actual dvHook
    ]
  where
    actual :: Attributes -> Either (Error ParseError) Hook
    actual = parseAttributes
    dvHook =
        Kore.Attributes
            [ (Kore.asKorePattern . Kore.ApplicationPattern)
                  Kore.Application
                      { applicationSymbolOrAlias = Hook.hookSymbol
                      , applicationChildren = [dv]
                      }
            ]
