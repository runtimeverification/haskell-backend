module Data.Kore.KoreHelpers (testId) where

import           Data.Kore.AST.Common

testId :: String -> Id level
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }
