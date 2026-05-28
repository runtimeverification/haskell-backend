{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause
-}
module Test.Booster.Syntax.Json.Externalise (
    test_externalise,
) where

import Data.ByteString.Char8 (ByteString)
import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base as Internal
import Booster.Syntax.Json.Externalise (externaliseTerm)
import Kore.Syntax.Json.Types as Syntax hiding (LeftRight (..), var)
import Test.Booster.Fixture (someSort)

test_externalise :: TestTree
test_externalise =
    testGroup
        "Externalising patterns"
        [ testInternalNameRewrite
        ]

{- | The externaliser rewrites booster's internal rule-bound-variable prefix
@Eq#@ into the kore-grammar-conformant form @EqInternal@ so JSON-encoded kore
patterns survive parsing by standards-conforming downstream tools. For set
variables (names carrying a leading @\@@), the @\@@ stays at position 0:
@Eq#\@VarK0@ → @\@EqInternalVarK0@.
-}
testInternalNameRewrite :: TestTree
testInternalNameRewrite =
    testGroup
        "Rewriting booster-internal variable names at the JSON boundary"
        [ check "Eq# prefix" "Eq#VarX" "EqInternalVarX"
        , check "Eq#@ prefix preserves leading @ at position 0" "Eq#@VarK0" "@EqInternalVarK0"
        , check "Eq# prefix on _Gen-style name" "Eq#Var_Gen0" "EqInternalVar_Gen0"
        , check "Non-prefix name unchanged" "VarY" "VarY"
        , check "Mid-name occurrence unchanged" "MyEqHashThing" "MyEqHashThing"
        , check "Plain set variable unchanged" "@VarK0" "@VarK0"
        ]
  where
    extName :: ByteString -> Text
    extName input =
        case externaliseTerm (Var Variable{variableSort = someSort, variableName = input}) of
            KJEVar (Id name) _ -> name
            other -> error $ "expected KJEVar from externaliseTerm, got: " <> show other

    check desc input expected =
        testCase desc $ expected @=? extName input
