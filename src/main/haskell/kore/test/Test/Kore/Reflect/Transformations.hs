module Test.Kore.Reflect.Transformations
    ( test_idTransformations
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Kore.AST.Identifier
                 ( AstLocation (..), Id (..) )
import           Kore.Reflect
                 ( reflect )
import qualified Kore.Reflect as Reflect
import           Kore.Reflect.Transform
                 ( Transformation (Transformation), transform )
import           Kore.Reflect.Transformations

test_idTransformations :: [TestTree]
test_idTransformations =
    [ testCase "Removes Id location"
        (assertEqual ""
            (Reflect.mkRawStruct "Id"
                [   (Reflect.mkStructField
                        "getId" (Reflect.mkValue "\"test\"")
                    )
                , Reflect.mkDeleted
                ]
            )
            (transform
                (Transformation [removeIdLocation])
                (reflect Id {getId = "test", idLocation = AstLocationTest})
            )
        )
    ]
