module Test.Kore.Reflect.Transform
    ( test_transform
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Kore.Reflect as Reflect
import           Kore.Reflect.Transform

test_transform :: [TestTree]
test_transform =
    [ testCase "Removes node"
        (assertEqual ""
            (Reflect.mkList [Reflect.mkDeleted])
            (transform
                (Transformation [delete Value])
                (Reflect.mkList [(Reflect.mkValue "\"test\"")])
            )
        )
    , testCase "Removes multiple nodes"
        (assertEqual ""
            (Reflect.mkList [Reflect.mkDeleted, Reflect.mkDeleted])
            (transform
                (Transformation [delete Value])
                (Reflect.mkList
                    [(Reflect.mkValue "\"test\""), (Reflect.mkValue "\"test\"")]
                )
            )
        )
    , testCase "Removes node inside structures"
        (assertEqual ""
            (Reflect.mkList
                [ Reflect.mkSum "test" [Reflect.mkDeleted]
                , Reflect.mkRawStruct "test" [Reflect.mkDeleted]
                , Reflect.mkStructField "test" Reflect.mkDeleted
                , Reflect.mkDeleted
                , Reflect.mkList [Reflect.mkDeleted]
                , Reflect.mkTuple [Reflect.mkDeleted]
                , Reflect.mkDeleted
                ]
            )
            (transform
                (Transformation [delete Value])
                (Reflect.mkList
                    [ Reflect.mkSum "test" [Reflect.mkValue "\"test\""]
                    , Reflect.mkRawStruct "test" [Reflect.mkValue "\"test\""]
                    , Reflect.mkStructField "test" (Reflect.mkValue "\"test\"")
                    , Reflect.mkValue "\"test\""
                    , Reflect.mkList [Reflect.mkValue "\"test\""]
                    , Reflect.mkTuple [Reflect.mkValue "\"test\""]
                    , Reflect.mkDeleted
                    ]
                )
            )
        )
    , testCase "Name matches names"
        (assertEqual ""
            (Reflect.mkList
                [ Reflect.mkSum "test" []
                , Reflect.mkDeleted
                , Reflect.mkStruct "test" []
                , Reflect.mkDeleted
                , Reflect.mkStructField "test" Reflect.mkDeleted
                , Reflect.mkDeleted
                , Reflect.mkValue "\"test\""
                , Reflect.mkValue "\"delme\""
                , Reflect.mkList []
                , Reflect.mkTuple []
                , Reflect.mkDeleted
                ]
            )
            (transform
                (Transformation [delete (Name "delme")])
                (Reflect.mkList
                    [ Reflect.mkSum "test" []
                    , Reflect.mkSum "delme" []
                    , Reflect.mkStruct "test" []
                    , Reflect.mkStruct "delme" []
                    , Reflect.mkStructField "test" Reflect.mkDeleted
                    , Reflect.mkStructField "delme" Reflect.mkDeleted
                    , Reflect.mkValue "\"test\""
                    , Reflect.mkValue "\"delme\""
                    , Reflect.mkList []
                    , Reflect.mkTuple []
                    , Reflect.mkDeleted
                    ]
                )
            )
        )
    , testCase "Index matches indexes"
        (assertEqual ""
            (Reflect.mkList
                [ Reflect.mkSum "test"
                    [ Reflect.mkValue "\"test\""
                    , Reflect.mkDeleted
                    , Reflect.mkValue "\"test\""
                    ]
                , Reflect.mkDeleted
                , Reflect.mkRawStruct "test"
                    [ Reflect.mkValue "\"test\""
                    , Reflect.mkDeleted
                    , Reflect.mkValue "\"test\""
                    ]
                , Reflect.mkStructField "test" Reflect.mkDeleted
                , Reflect.mkValue "\"test\""
                , Reflect.mkList
                    [ Reflect.mkValue "\"test\""
                    , Reflect.mkDeleted
                    , Reflect.mkValue "\"test\""
                    ]
                , Reflect.mkTuple
                    [ Reflect.mkValue "\"test\""
                    , Reflect.mkDeleted
                    , Reflect.mkValue "\"test\""
                    ]
                , Reflect.mkDeleted
                ]
            )
            (transform
                (Transformation
                    [descend Any (Transformation [delete (Index 1)])]
                )
                (Reflect.mkList
                    [ Reflect.mkSum "test"
                        [ Reflect.mkValue "\"test\""
                        , Reflect.mkValue "\"delme\""
                        , Reflect.mkValue "\"test\""
                        ]
                    , Reflect.mkValue "\"delme\""
                    , Reflect.mkRawStruct "test"
                        [ Reflect.mkValue "\"test\""
                        , Reflect.mkValue "\"delme\""
                        , Reflect.mkValue "\"test\""
                        ]
                    , Reflect.mkStructField "test" Reflect.mkDeleted
                    , Reflect.mkValue "\"test\""
                    , Reflect.mkList
                        [ Reflect.mkValue "\"test\""
                        , Reflect.mkValue "\"delme\""
                        , Reflect.mkValue "\"test\""
                        ]
                    , Reflect.mkTuple
                        [ Reflect.mkValue "\"test\""
                        , Reflect.mkValue "\"delme\""
                        , Reflect.mkValue "\"test\""
                        ]
                    , Reflect.mkDeleted
                    ]
                )
            )
        )
    , testCase "Value matches only values"
        (assertEqual ""
            (Reflect.mkList
                [ Reflect.mkSum "test" []
                , Reflect.mkStruct "test" []
                , Reflect.mkStructField "test" Reflect.mkDeleted
                , Reflect.mkDeleted
                , Reflect.mkList []
                , Reflect.mkTuple []
                , Reflect.mkDeleted
                ]
            )
            (transform
                (Transformation [delete Value])
                (Reflect.mkList
                    [ Reflect.mkSum "test" []
                    , Reflect.mkStruct "test" []
                    , Reflect.mkStructField "test" Reflect.mkDeleted
                    , Reflect.mkValue "\"test\""
                    , Reflect.mkList []
                    , Reflect.mkTuple []
                    , Reflect.mkDeleted
                    ]
                )
            )
        )
    , testCase "Any matches everything"
        (assertEqual ""
            (Reflect.mkList
                [ Reflect.mkDeleted
                , Reflect.mkDeleted
                , Reflect.mkDeleted
                , Reflect.mkDeleted
                , Reflect.mkDeleted
                , Reflect.mkDeleted
                , Reflect.mkDeleted
                ]
            )
            (transform
                (Transformation
                    [descend Any (Transformation [delete Any])]
                )
                (Reflect.mkList
                    [ Reflect.mkSum "test" []
                    , Reflect.mkStruct "test" []
                    , Reflect.mkStructField "test" Reflect.mkDeleted
                    , Reflect.mkValue "\"test\""
                    , Reflect.mkList []
                    , Reflect.mkTuple []
                    , Reflect.mkDeleted
                    ]
                )
            )
        )
    ]
