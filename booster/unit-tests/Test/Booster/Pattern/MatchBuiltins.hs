{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Unit tests for booster's matcher on builtin collections — currently
scoped to non-empty 'Set' patterns.  These tests pin today's matcher
behaviour: 'matchSets' (Pattern.Match) returns 'MatchIndeterminate'
for any non-empty set on either side, so every simplification rule
whose LHS mentions 'SetItem(...)' or set union '_|Set_' is dead in
booster-dev.

The companion RPC reproducer lives at
'booster/test/rpc-integration/test-set-matching'.

A future fix should:

  * decide concrete-vs-concrete sets by multiset equality,
  * commit on a single 'SetItem(...)' + frame variable pattern when the
    subject has exactly one syntactically compatible element,
  * keep returning 'MatchIndeterminate' on multi-match ambiguity (no
    pairwise n-way matching).

After the fix lands the decisive cases flip from 'indet' to 'success'
(or 'failed'); the multi-match cases remain 'indet' as a regression
guard against an over-eager fix.
-}
module Test.Booster.Pattern.MatchBuiltins (
    test_match_builtins,
) where

import Data.ByteString.Char8 qualified as BS
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Pattern.Match
import Test.Booster.Fixture

test_match_builtins :: TestTree
test_match_builtins =
    testGroup
        "Builtin collection matching"
        [ internalSetsMatching
        ]

internalSetsMatching :: TestTree
internalSetsMatching =
    testGroup
        "matchSets: non-empty sets are Indeterminate today"
        [ -- Concrete singleton ~ concrete singleton.
          -- Today: matchSets bails Indeterminate because patElements /= [].
          -- After fix: MatchSuccess with no new bindings (multiset eq decides it).
          test
            "concrete singleton ~ concrete singleton"
            (kset [dvN 5] Nothing)
            (kset [dvN 5] Nothing)
            (indet (kset [dvN 5] Nothing) (kset [dvN 5] Nothing))
        , -- Concrete two-element ~ same concrete two-element.
          -- Today: Indeterminate.  After fix: MatchSuccess (multiset eq).
          test
            "concrete two-element ~ same concrete two-element"
            (kset [dvN 5, dvN 6] Nothing)
            (kset [dvN 5, dvN 6] Nothing)
            (indet (kset [dvN 5, dvN 6] Nothing) (kset [dvN 5, dvN 6] Nothing))
        , -- Frame + literal ~ concrete singleton with matching element.
          -- Canonical "one called-out element + frame variable" shape — the
          -- KEVM membership lemma family ('X in (REST |Set SetItem(Y:Int))').
          -- Today: Indeterminate.  After fix: MatchSuccess with REST -> .Set.
          test
            "frame + literal ~ concrete singleton"
            (kset [dvN 7] (Just (var "REST" setSort)))
            (kset [dvN 7] Nothing)
            (indet (kset [dvN 7] (Just (var "REST" setSort))) (kset [dvN 7] Nothing))
        , -- Frame + variable element ~ concrete two-element set.  Multi-match
          -- ambiguity: 'Y' could bind to either 5 or 6, both sound but distinct.
          -- After the fix this MUST stay Indeterminate — a sound matcher bails
          -- on multi-match rather than picking arbitrarily.
          test
            "frame + variable element ~ concrete two-element set (multi-match: stays Indeterminate)"
            (kset [var "Y" someSort] (Just (var "REST" setSort)))
            (kset [dvN 5, dvN 6] Nothing)
            (indet (kset [var "Y" someSort] (Just (var "REST" setSort))) (kset [dvN 5, dvN 6] Nothing))
        , -- Frame + literal ~ frame + same literal.
          -- Today: Indeterminate.  After fix: MatchSuccess with patRest -> subjRest.
          test
            "frame + literal ~ frame + same literal"
            (kset [dvN 7] (Just (var "REST" setSort)))
            (kset [dvN 7] (Just (var "A" setSort)))
            (indet (kset [dvN 7] (Just (var "REST" setSort))) (kset [dvN 7] (Just (var "A" setSort))))
        , -- Dedup multi-match: 'A:Set |Set SetItem(1) |Set SetItem(1)' has two
          -- identical literal elements.  After fix this stays Indeterminate.
          test
            "frame + variable element ~ frame + duplicate literals (multi-match dedup: stays Indeterminate)"
            (kset [var "X" someSort] (Just (var "S" setSort)))
            (kset [dvN 1, dvN 1] (Just (var "A" setSort)))
            ( indet
                (kset [var "X" someSort] (Just (var "S" setSort)))
                (kset [dvN 1, dvN 1] (Just (var "A" setSort)))
            )
        ]

----------------------------------------
-- helpers

kset :: [Term] -> Maybe Term -> Term
kset elems rest = KSet testKSetDef elems rest

dvN :: Int -> Term
dvN n = dv someSort (BS.pack (show n))

test :: String -> Term -> Term -> MatchResult -> TestTree
test name pat subj expected =
    testCase name $ matchTerms Eval testDefinition pat subj @?= expected

indet :: Term -> Term -> MatchResult
indet p s = MatchIndeterminate Map.empty (NE.singleton (p, s))
