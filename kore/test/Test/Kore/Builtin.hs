module Test.Kore.Builtin
    ( test_internalize ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Kore
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.TermLike

import qualified Test.Kore.Builtin.Builtin as Builtin
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Int
import qualified Test.Kore.Builtin.List as List

test_internalize :: [TestTree]
test_internalize =
    [ internalizes  "unitList"
        unitList
        (mkList [])
    , internalizes  "elementList"
        (elementList (mkInt 0))
        (mkList [mkInt 0])
    , internalizes  "concatList(internal, internal)"
        (concatList (mkList [mkInt 0]) (mkList [mkInt 1]))
        (mkList [mkInt 0, mkInt 1])
    , internalizes  "concatList(element, element)"
        (concatList (elementList (mkInt 0)) (elementList (mkInt 1)))
        (mkList [mkInt 0, mkInt 1])
    , internalizes  "concatList(element, unit)"
        (concatList (elementList (mkInt 0)) unitList)
        (mkList [mkInt 0])
    , internalizes  "concatList(unit, element)"
        (concatList unitList (elementList (mkInt 1)))
        (mkList [mkInt 1])
    ]
  where
    unitList = Builtin.unitList
    elementList = Builtin.elementList
    concatList = Builtin.concatList
    mkList = List.asInternal
    mkInt = Int.asInternal

withInternalized
    :: (TermLike Variable -> Assertion)
    -> TestName
    -> TermLike Variable
    -> TestTree
withInternalized check name origin =
    testCase name (check $ Kore.internalize metadata origin)

internalizes
    :: TestName
    -> TermLike Variable
    -> TermLike Variable
    -> TestTree
internalizes name origin expect =
    withInternalized (assertEqual "" expect) name origin

metadata :: SmtMetadataTools Attribute.Symbol
metadata = Builtin.testMetadataTools
