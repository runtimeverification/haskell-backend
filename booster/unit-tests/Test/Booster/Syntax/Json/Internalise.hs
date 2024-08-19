{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Syntax.Json.Internalise (
    test_internalise,
) where

import Control.Monad.Trans.Except
import Data.Coerce
import Data.Map qualified as Map
import Data.Text (Text)
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base as Internal
import Booster.Pattern.Bool as Internal
import Booster.Syntax.Json.Internalise
import Kore.Syntax.Json.Types as Syntax hiding (LeftRight (..), var)
import Test.Booster.Fixture

test_internalise :: TestTree
test_internalise =
    testGroup
        "Internalising patterns"
        [ testBasicPredicates
        , testSubstitutions
        ]

testBasicPredicates :: TestTree
testBasicPredicates =
    testGroup
        "Internalising different kinds of predicates"
        [ shouldBeBool
            "basic boolean predicate (simply false)"
            (KJEquals boolSort' someSort' (KJDV boolSort' "true") (KJDV boolSort' "false"))
            (coerce FalseBool)
        , -- tricky cases
          let notAndCeil =
                KJNot someSort' . KJAnd someSort' $
                    [ KJCeil boolSort' someSort' $ KJDV boolSort' "true"
                    , KJEquals boolSort' someSort' (KJDV boolSort' "true") (KJDV boolSort' "false")
                    ]
           in expectUnsupported
                "conjunction under a not with ceil and an equation"
                notAndCeil
                notAndCeil
        ]
  where
    internaliseAll = internalisePredicates DisallowAlias IgnoreSubsorts Nothing testDefinition
    internalise = internaliseAll . (: [])

    shouldBeBool name pat expected =
        testCase name $
            Right (InternalisedPredicates [expected] mempty mempty [])
                @=? runExcept (internalise pat)

    expectUnsupported description pat expected =
        testCase ("Unsupported: " <> description) $
            Right (InternalisedPredicates mempty mempty mempty [expected])
                @=? runExcept (internalise pat)

testSubstitutions :: TestTree
testSubstitutions =
    testGroup
        "Recognising and checking substitutions"
        [ test
            "Basic substitution equation"
            ("X" .==> dv' "something")
            (hasSubstitution [("X", dv someSort "something")])
        , test
            "Several substitutions"
            ( equations'
                [ "X" .==> dv' "something"
                , "Y" .==> dv' "something-else"
                ]
            )
            ( hasSubstitution
                [ ("X", dv someSort "something")
                , ("Y", dv someSort "something-else")
                ]
            )
        , let varX = var "X" someSort
           in test
                "X => f(X) is not a substitution"
                ("X" .==> app' "f1" [var' "X"])
                (hasEquations [(varX, app f1 [varX])])
        , let var_ = flip var someSort
           in test
                "Circular references in substitutions are broken up"
                ( equations'
                    [ "X" .==> app' "con1" [var' "Y"]
                    , "Y" .==> app' "con2" [var' "Z"]
                    , "Z" .==> app' "f1" [var' "X"]
                    ]
                )
                ( hasEquations [(var_ "X", app con1 [var_ "Y"])]
                    .<> hasSubstitution [("Y", app con2 [var_ "Z"]), ("Z", app f1 [var_ "X"])]
                )
        , let var_ = flip var someSort
           in test
                "Ambiguous substitutions are turned into equations"
                ( equations'
                    [ "X" .==> var' "Y"
                    , "X" .==> var' "Z"
                    ]
                )
                (hasEquations [(var_ "X", var_ "Z"), (var_ "X", var_ "Y")])
        ]
  where
    test name syntax expected =
        testCase name $
            Right expected @=? internalise [syntax]
    internalise =
        runExcept . internalisePredicates DisallowAlias IgnoreSubsorts Nothing testDefinition

    var' name = KJEVar (Id name) someSort'
    app' sym = KJApp (Id sym) []

    hasSubstitution pairs =
        let expectedSubstitution =
                Map.fromList [(Variable someSort v, t) | (v, t) <- pairs]
         in InternalisedPredicates mempty mempty expectedSubstitution mempty

    hasEquations pairs =
        InternalisedPredicates [t ==. t' | (t, t') <- pairs] mempty mempty mempty

-- basically a semigroup instance but in the general case the
-- substitutions would have to be trimmed. We don't need it in the
-- main code (could cause inefficiencies) so it lives here.
(.<>) :: InternalisedPredicates -> InternalisedPredicates -> InternalisedPredicates
ps1 .<> ps2 =
    InternalisedPredicates
        { boolPredicates = ps1.boolPredicates <> ps2.boolPredicates
        , ceilPredicates = ps1.ceilPredicates <> ps2.ceilPredicates
        , substitution =
            Map.unionWithKey (\k _ _ -> error ("Duplicate key " <> show k)) ps1.substitution ps2.substitution
        , unsupported = ps1.unsupported <> ps2.unsupported
        }

(.==>) :: Text -> Syntax.KorePattern -> Syntax.KorePattern
v .==> t' = KJEquals someSort' someSort' (KJEVar (Id v) someSort') t'

dv' :: Text -> Syntax.KorePattern
dv' = KJDV someSort'

equations' :: [Syntax.KorePattern] -> Syntax.KorePattern
equations' = KJAnd someSort'

-- syntax equivalents of sorts in testDefinition
someSort', boolSort' {- , intSort' -} :: Syntax.Sort
someSort' = Syntax.SortApp (Id "SomeSort") []
boolSort' = Syntax.SortApp (Id "SortBool") []

-- intSort' = Syntax.SortApp (Id "SortInt") []

-- produces a K-equals predicate
(==.) :: Internal.Term -> Internal.Term -> Internal.Predicate
t ==. t' = Predicate $ SymbolApplication eqK [] [inDotK t, inDotK t']
  where
    inDotK :: Internal.Term -> Internal.Term
    inDotK x = SymbolApplication kseq [] [inj someSort kItemSort x, SymbolApplication dotk [] []]
