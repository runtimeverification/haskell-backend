{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Test.Kore.Error where

import Test.Tasty
import Test.Terse

import Data.Void
    ( Void
    )
import Kore.Error
    ( Error
    , assertRight
    , koreError
    , printError
    )

{-
   Considerable code uses an `Either (Error a) b` type.
   To simplify code, we use concrete types and `mkLeft`
   and `mkRight` helpers.
-}

type Wrapper = Either (Error DontCare) String
type DontCare = Void



test_assertRight :: TestTree
test_assertRight =
    testGroup "assertRight"
        [ run (mkRight "expected") `equals_` "expected"
        , run (mkLeft   someError) `throws_` printError someError
        ]
      where
        run = assertRight
        someError = koreError "the error message"


mkRight :: String -> Wrapper
mkRight = Right

mkLeft :: Error DontCare -> Wrapper
mkLeft = Left
