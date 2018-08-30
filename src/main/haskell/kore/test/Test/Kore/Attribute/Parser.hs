module Test.Kore.Attribute.Parser where

import Test.Tasty ( TestTree )
import Test.Tasty.HUnit ( Assertion, (@=?), testCase )

import qualified Data.Foldable as Foldable

import Kore.Attribute.Parser
import qualified Kore.AST.Common as Kore
import qualified Kore.AST.Kore as Kore
import qualified Kore.AST.PureML as Kore
import qualified Kore.AST.Sentence as Kore
import qualified Kore.Error
import qualified Kore.Implicit.Attributes as Kore

-- | Demonstrate that two parsers are equivalent under the same attributes.
equiv :: (Eq a, Show a) => Kore.Attributes -> Parser a -> Parser a -> Assertion
equiv attrs expected actual =
    runParser expected attrs @=? runParser actual attrs

emptyAttrs :: Kore.Attributes
emptyAttrs = Kore.Attributes []

test_runParser :: [TestTree]
test_runParser =
    [ let
        expect = reject
        actual = ok
        attrs =
            Kore.Attributes [ Kore.asKorePattern metaPattern ]
          where
            metaPattern = Kore.StringLiteralPattern (Kore.StringLiteral "meta-pattern")
      in
        testCase "Rejects meta-level attribute patterns"
            (equiv attrs expect actual)
    , let
        expect = reject
        actual = ok
        attrs = dvAttrs
      in
        testCase "Rejects non-application attribute patterns"
            (equiv attrs expect actual)
    , let
        expect = pure [[], []]
        actual = map getOccurrence . Foldable.toList <$> parseAttribute "key"
        attrs = multipleAttrs
      in
        testCase "Accepts multiple occurrences of the same attribute"
            (equiv attrs expect actual)
    ]
  where
    reject = Kore.Error.koreFail "Expected object-level application pattern"
    ok = pure ()

key :: Kore.CommonKorePattern
key = Kore.keyOnlyAttribute "key"

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
                (Kore.asPurePattern . Kore.StringLiteralPattern)
                    (Kore.StringLiteral "true")
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
                  { applicationSymbolOrAlias = Kore.attributeHead "hook"
                  , applicationChildren = [char]
                  }
        ]

test_choose :: [TestTree]
test_choose =
    [ let
        expect = first
        actual = choose first second
      in
        testCase "Throws first error"
            (equiv attrs expect actual)
    , let
        expect = ok
        actual = choose ok impossible
      in
        testCase "Does not evaluate second parser if first succeeds"
            (equiv attrs expect actual)
    , let
        expect = ok
        actual = choose first ok
      in
        testCase "Ignores first failure if second succeeds"
            (equiv attrs expect actual)
    , let
        expect = inContext first
        actual = choose expect second
      in
        testCase "Preserves context"
            (equiv attrs expect actual)
    ]
  where
    attrs = emptyAttrs
    first :: Parser ()
    first = Kore.Error.koreFail "First error"
    second :: Parser ()
    second = Kore.Error.koreFail "Second error"
    impossible = error "The impossible happened!"
    inContext = withContext "attribute"
    ok = pure ()

test_parseStringAttribute :: [TestTree]
test_parseStringAttribute =
    [ testCase "Rejects literal character arguments"
        (equiv charHook rejectChar ok)
    , testCase "Rejects object-level arguments"
        (equiv dvHook rejectObject ok)
    ]
  where
    rejectChar =
        withContext "hook"
            (Kore.Error.koreFail "Expected literal string argument")
    rejectObject =
        withContext "hook"
            (Kore.Error.koreFail "Expected meta pattern")
    ok = parseStringAttribute "hook"
    dvHook =
        Kore.Attributes
            [ (Kore.asKorePattern . Kore.ApplicationPattern)
                  Kore.Application
                      { applicationSymbolOrAlias = Kore.attributeHead "hook"
                      , applicationChildren = [dv]
                      }
            ]

test_assertNoAttribute :: [TestTree]
test_assertNoAttribute =
    [ testCase "Fails if attribute is present"
        (equiv keyAttrs expect actual)
    ]
  where
    expect = Kore.Error.koreFail "Expected no attribute 'key'"
    actual = assertNoAttribute "key"

test_assertKeyOnlyAttribute :: [TestTree]
test_assertKeyOnlyAttribute =
    [ let
        actual = assertKeyOnlyAttribute "key"
        expect =
            withContext "key"
                (Kore.Error.koreFail "Unexpected multiple occurrences")
      in
        testCase "Fails if attribute is occurs multiple times"
            (equiv multipleAttrs expect actual)
    , let
        actual = assertKeyOnlyAttribute "hook"
        expect =
            withContext "hook"
                (Kore.Error.koreFail "Unexpected arguments")
      in
        testCase "Fails if attribute has arguments"
            (equiv charHook expect actual)
    , let
        actual = assertKeyOnlyAttribute "key"
        expect = Kore.Error.koreFail "No attribute found matching: key"
        attrs = emptyAttrs
      in
        testCase "Fails if attribute is missing" (equiv attrs expect actual)
    ]
