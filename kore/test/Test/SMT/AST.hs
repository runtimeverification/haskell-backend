module Test.SMT.AST (test_parseSexpr) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import qualified Text.Megaparsec as Parser

import SMT.AST

test_parseSexpr :: [TestTree]
test_parseSexpr =
    [ testCase "parse atom" $
        assertEqual ""
            (Right [Atom "a"])
            (Parser.runParser parseSExprFile "fileName" "a")
    ,  testCase "parse atom with spaces" $
        assertEqual ""
            (Right [Atom "a"])
            (Parser.runParser parseSExprFile "fileName" " a ")
    ,  testCase "parse atom with comment" $
        assertEqual ""
            (Right [Atom "a"])
            (Parser.runParser parseSExprFile "fileName" ";comment\n a ")
    , testCase "parse list" $
        assertEqual ""
            (Right [List [Atom "a", Atom "b"]])
            (Parser.runParser parseSExprFile "fileName" "(a b)")
    , testCase "parse list with spaces" $
        assertEqual ""
            (Right [List [Atom "a", Atom "b"]])
            (Parser.runParser parseSExprFile "fileName" " (a b) ")
    , testCase "parse list in list" $
        assertEqual ""
            (Right [List [Atom "a", List [Atom "b", Atom "c"]]])
            (Parser.runParser parseSExprFile "fileName" " (a (b c)) ")
    , testCase "parse multiple sexpr" $
        assertEqual ""
            (Right [Atom "a", Atom "b"])
            (Parser.runParser parseSExprFile "fileName" "a\nb")
    , testCase "parse multiple sexpr with spaces and comments" $
        assertEqual ""
            (Right [Atom "a", Atom "b"])
            (Parser.runParser parseSExprFile "fileName" ";comment\na;c\nb;")
    ]
