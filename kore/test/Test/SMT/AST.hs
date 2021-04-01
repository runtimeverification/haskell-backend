{-# LANGUAGE Strict #-}

module Test.SMT.AST (
    test_parseSExpr,
) where

import Data.Text (
    Text,
 )
import Prelude.Kore
import SMT.AST
import Test.Tasty
import Test.Tasty.HUnit
import qualified Text.Megaparsec as Parser

test_parseSExpr :: [TestTree]
test_parseSExpr =
    [ parse "atom" [Atom "a"] "a"
    , parse "atom with whitespace" [Atom "a"] " a "
    , parse "atom with comment" [Atom "a"] ";comment\n a "
    , parse "list" [List [Atom "a", Atom "b"]] "(a b)"
    , parse "list with whitespace" [List [Atom "a", Atom "b"]] " (a b) "
    , parse
        "nested list"
        [List [Atom "a", List [Atom "b", Atom "c"]]]
        " (a (b c)) "
    , parse "multiple S-expressions" [Atom "a", Atom "b"] "a\nb"
    , parse
        "multiple S-expressions with whitespace and comments"
        [Atom "a", Atom "b"]
        ";comment\na;c\nb;"
    , parse
        "(ite (< #1 #2) #1 #2)"
        [ List
            [ Atom "ite"
            , List [Atom "<", Atom "#1", Atom "#2"]
            , Atom "#1"
            , Atom "#2"
            ]
        ]
        "(ite (< #1 #2) #1 #2)"
    ]
  where
    parse ::
        HasCallStack =>
        TestName ->
        [SExpr] ->
        Text ->
        TestTree
    parse testName results input =
        testCase testName $
            assertEqual "" (Right results) $
                Parser.runParser parseSExprFile "<string>" input
