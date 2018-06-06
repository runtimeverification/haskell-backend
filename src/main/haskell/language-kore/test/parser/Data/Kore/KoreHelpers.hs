module Data.Kore.KoreHelpers (testId) where

import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence

testId :: String -> Id level
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }
