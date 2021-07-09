{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Test.Kore.Error (
    test_assertRight,
) where

import Data.Void (
    Void,
 )
import Kore.Error (
    Error,
    assertRight,
    koreError,
    printError,
 )
import Prelude.Kore
import Test.Tasty
import Test.Terse

{-
   Considerable code uses an `Either (Error a) b` type.
   To simplify code, we use concrete types and `mkLeft`
   and `mkRight` helpers.
-}

type Wrapper = Either (Error DontCare) String
type DontCare = Void

test_assertRight :: TestTree
test_assertRight =
    testGroup
        "assertRight"
        [ run (mkRight "expected") `equals_` "expected"
        , run (mkLeft someError) `throws_` printError someError
        ]
  where
    run = assertRight
    someError = koreError "the error message"

mkRight :: String -> Wrapper
mkRight = Right

mkLeft :: Error DontCare -> Wrapper
mkLeft = Left
