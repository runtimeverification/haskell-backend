module Data.Kore.IndentingPrinterTest (indentingPrinterTests) where

import           Data.Kore.IndentingPrinter
import           Data.List                  (intersperse)

import           Test.Tasty                 (TestTree, testGroup)
import           Test.Tasty.HUnit           (assertEqual, testCase)

class TestPrinter a where
    testPrint :: PrinterOutput w m => a -> m ()

stringTest :: TestPrinter a => a -> StringPrinter ()
stringTest = testPrint

testPrintToString :: TestPrinter a => a -> String
testPrintToString a = printToString (stringTest a)

instance TestPrinter Integer where
    testPrint = write . show

newtype IntList = IntList [Integer]

instance TestPrinter IntList where
    testPrint (IntList []) =
        do
            write "["
            betweenLines
            write "]"
    testPrint (IntList list) =
        do
            write "["
            withIndent
                2
                (betweenLines >> sequence_ intPrintsWithSeparators)
            betweenLines
            write "]"
      where
        intPrints = map testPrint list
        intPrintsWithSeparators =
            intersperse (write "," >> betweenLines) intPrints

indentingPrinterTests :: TestTree
indentingPrinterTests =
    testGroup
        "IndentingPrinter unit tests"
        [ testCase
            "Simple serialization"
            (assertEqual "Expecting no frills serialization!"
                "10"
                (testPrintToString (10 :: Integer))
            )
        , testCase
            "Serialization with multiple lines"
            (assertEqual "Expecting multiple lines!"
                "[\n]"
                (testPrintToString (IntList []))
            )
        , testCase
            "Serialization with indentation and multiple lines"
            (assertEqual "Expecting multiple lines!"
                "[\n  10,\n  11\n]"
                (testPrintToString (IntList [10, 11]))
            )
        ]
