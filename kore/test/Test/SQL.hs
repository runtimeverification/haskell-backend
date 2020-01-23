module Test.SQL
    ( testTable
    , test_EitherIntInt
    , test_Unit
    , test_MaybeInt
    ) where

import Test.Tasty

import Data.Int
    ( Int64
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import SQL

import Test.Tasty.HUnit.Ext

testTable :: forall table. Table table => [table] -> TestTree
testTable rows =
    testCase "" . runTestSQL $ do
        -- create the table
        createTable (Proxy @table)
        -- insert (unique) rows
        keys1 <- traverse insertUniqueRow rows
        -- select the rows which were just inserted
        keys2 <- traverse selectRow rows
        -- assert that the inserted and selected keys are the same
        assertEqual "expected to select inserted keys" (Just <$> keys1) keys2

runTestSQL :: SQL a -> IO a
runTestSQL = runSQL ":memory:"

-- | Test of the generic instance for a simple sum type.
test_EitherIntInt :: TestTree
test_EitherIntInt =
    testTable
        [ EitherIntInt (Left 0)
        , EitherIntInt (Right 1)
        , EitherIntInt (Right 2)
        ]

newtype EitherIntInt = EitherIntInt { unEitherIntInt :: Either Int64 Int64 }
    deriving (GHC.Generic)

instance Table EitherIntInt where
    createTable = createTableUnwrapped
    insertRow = insertRowUnwrapped
    selectRow = selectRowUnwrapped

instance SOP.Generic EitherIntInt

instance SOP.HasDatatypeInfo EitherIntInt

-- | Test of the generic instance for a unitary constructor.
test_Unit :: TestTree
test_Unit =
    testTable [ Unit ]

data Unit = Unit
    deriving (GHC.Generic)

instance Table Unit where
    createTable = createTableGeneric
    insertRow = insertRowGeneric
    selectRow = selectRowGeneric

instance SOP.Generic Unit

instance SOP.HasDatatypeInfo Unit

-- | Test of the generic instance for a sum type with a unitary constructor.
test_MaybeInt :: TestTree
test_MaybeInt =
    testTable
        [ MaybeInt (Just 0)
        , MaybeInt (Just 1)
        , MaybeInt (Just 2)
        , MaybeInt Nothing
        ]

newtype MaybeInt = MaybeInt { unMaybeInt :: Maybe Int64 }
    deriving (GHC.Generic)

instance Table MaybeInt where
    createTable = createTableUnwrapped
    insertRow = insertRowUnwrapped
    selectRow = selectRowUnwrapped

instance SOP.Generic MaybeInt

instance SOP.HasDatatypeInfo MaybeInt
