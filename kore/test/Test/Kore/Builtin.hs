module Test.Kore.Builtin
    ( test_internalize ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map
import           Prelude hiding
                 ( concatMap )

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Kore
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.TermLike

import qualified Test.Kore.Builtin.Builtin as Builtin
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Int
import qualified Test.Kore.Builtin.List as List
import qualified Test.Kore.Builtin.Map as Map

test_internalize :: [TestTree]
test_internalize =
    [ internalizes  "unitList"
        unitList
        (mkList [])
    , internalizes  "elementList"
        (elementList zero)
        (mkList [zero])
    , internalizes  "concatList(internal, internal)"
        (concatList (mkList [zero]) (mkList [one]))
        (mkList [zero, one])
    , internalizes  "concatList(element, element)"
        (concatList (elementList zero) (elementList one))
        (mkList [zero, one])
    , internalizes  "concatList(element, unit)"
        (concatList (elementList zero) unitList)
        (mkList [zero])
    , internalizes  "concatList(unit, element)"
        (concatList unitList (elementList one))
        (mkList [one])

    , internalizes  "unitMap"
        unitMap
        (mkMap [])
    , internalizes  "elementMap"
        (elementMap zero one)
        (mkMap [(zero, one)])
    , internalizes  "concatMap(internal, internal)"
        (concatMap (mkMap [(zero, one)]) (mkMap [(one, two)]))
        (mkMap [(zero, one), (one, two)])
    , internalizes  "concatMap(element, element)"
        (concatMap (elementMap zero one) (elementMap one two))
        (mkMap [(zero, one), (one, two)])
    , internalizes  "concatMap(element, unit)"
        (concatMap (elementMap zero one) unitMap)
        (mkMap [(zero, one)])
    , internalizes  "concatMap(unit, element)"
        (concatMap unitMap (elementMap one two))
        (mkMap [(one, two)])
    ]
  where
    unitList = Builtin.unitList
    elementList = Builtin.elementList
    concatList = Builtin.concatList
    mkList = List.asInternal
    unitMap = Builtin.unitMap
    elementMap = Builtin.elementMap
    concatMap = Builtin.concatMap
    mkMap = Map.asInternal . Data.Map.fromList

    mkInt :: Ord variable => Integer -> TermLike variable
    mkInt = Int.asInternal
    zero, one, two :: Ord variable => TermLike variable
    zero = mkInt 0
    one = mkInt 1
    two = mkInt 2

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
