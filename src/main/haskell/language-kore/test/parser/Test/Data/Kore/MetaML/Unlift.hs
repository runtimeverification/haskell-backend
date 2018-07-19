-- TODO(traiansf): add more negative tests
module Test.Data.Kore.MetaML.Unlift (test_unlift) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Test.Data.Kore.MetaML.Lift
       ( prettyAssertEqual, variablePattern )

import Data.Fix
import Data.Kore.AST.Common
import Data.Kore.AST.Kore
import Data.Kore.AST.MetaOrObject
import Data.Kore.AST.PureML
import Data.Kore.AST.PureToKore
import Data.Kore.Implicit.ImplicitSorts
import Data.Kore.MetaML.AST
import Data.Kore.MetaML.Unlift

test_unlift :: [TestTree]
test_unlift =
    [ testCase "Failing to unlift to Id 1"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta
                (Fix (StringLiteralPattern (StringLiteral "")))
            ::Maybe (Id Object))
        )
    , testCase "Failing to unlift to Id 2"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta
                (Fix (StringLiteralPattern (StringLiteral "#a")))
            ::Maybe (Id Object))
        )
    , testCase "Failing to unlift to Id 0"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta (variablePattern "#a" sortMetaSort)
            ::Maybe (Id Object))
        )
    , testCase "Failing to unlift to SortVariable 0"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta (variablePattern "#`a" sortMetaSort)
            ::Maybe (SortVariable Object))
        )
    , testCase "Failing to unlift to SortActual 0"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta (variablePattern "#`a" sortMetaSort)
            ::Maybe (SortActual Object))
        )
    , testCase "Failing to unlift to Sort 0"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta (variablePattern "#`a" sortMetaSort)
            ::Maybe (Sort Object))
        )
    , testCase "Failing to unlift to [Sort] 0"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta (variablePattern "#`a" sortMetaSort)
            ::Maybe [Sort Object])
        )
    , testCase "Failing to unlift to Variable 0"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta (variablePattern "#`a" sortMetaSort)
            ::Maybe (Variable Object))
        )
    , testCase "Failing to unlift to [CommonMetaPattern] 0"
        (prettyAssertEqual "" Nothing
            (unliftFromMeta (variablePattern "#`a" sortMetaSort)
            ::Maybe [CommonMetaPattern])
        )
    , testCase "Unlift to asKorePattern"
        (let
            metaPattern =
                Fix
                    (apply consSortListHead
                        [variablePattern "#`a" sortMetaSort]
                    )
        in
            prettyAssertEqual ""
                (Just (patternPureToKore metaPattern))
                (unliftFromMeta metaPattern :: Maybe CommonKorePattern)
        )
    ]

