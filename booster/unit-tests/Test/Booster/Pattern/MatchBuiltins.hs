{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Unit tests for booster's matcher on builtin collections — currently
scoped to non-empty 'Set' patterns.  These pin the decisive cases
('matchSets' commits on concrete-vs-concrete multiset equality and on
a single 'SetItem(literal)' + frame variable pattern against a unique
syntactic candidate) while keeping multi-match ambiguity as
'MatchIndeterminate' (no n-way pairwise matching).

The companion RPC reproducer lives at
'booster/test/rpc-integration/test-set-matching'.
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
        "matchSets"
        [ -- Frameless singleton with a non-concrete pattern element against a
          -- concrete singleton subject.  Today: case (2)'s 'isConcrete patElements'
          -- guard fails, no other case applies, falls through to indeterminate.
          -- After the Gap-C fix: recurse on the elements via 'enqueueRegularProblem'
          -- and bind Y to the subject DV.
          test
            "Gap C: variable singleton ~ concrete singleton (frameless)"
            (kset [var "Y" someSort] Nothing)
            (kset [dvN 7] Nothing)
            (success [("Y", someSort, dvN 7)])
        , -- Same Gap-C shape with the pattern element wrapped in an injection.
          -- This is the canonical KEVM membership-lemma shape after
          -- 'matchSymbolApplications' descends through the '_|Set_' operands:
          -- 'SetItem(inj{Int,KItem}(Y)) ~ SetItem(inj{Int,KItem}(N))' reduces to
          -- frameless 'KSet [inj Y] Nothing ~ KSet [inj N] Nothing'.
          test
            "Gap C: inj-wrapped variable singleton ~ inj-wrapped concrete singleton (frameless)"
            (kset [inj aSubsort someSort (var "Y" aSubsort)] Nothing)
            (kset [inj aSubsort someSort (dv aSubsort "7")] Nothing)
            (success [("Y", aSubsort, dv aSubsort "7")])
        , -- Gap-C with two distinct variables on opposite sides of a frameless
          -- singleton match.  Recursion handles it via 'bindVariable'.
          test
            "Gap C: variable singleton ~ different variable singleton (frameless)"
            (kset [var "Y" someSort] Nothing)
            (kset [var "Z" someSort] Nothing)
            (success [("Y", someSort, var "Z" someSort)])
        , -- Concrete singleton ~ concrete singleton: multiset equality decides
          -- it, no new bindings introduced.
          test
            "concrete singleton ~ concrete singleton"
            (kset [dvN 5] Nothing)
            (kset [dvN 5] Nothing)
            (success [])
        , -- Concrete two-element ~ same concrete two-element: multiset equality.
          test
            "concrete two-element ~ same concrete two-element"
            (kset [dvN 5, dvN 6] Nothing)
            (kset [dvN 5, dvN 6] Nothing)
            (success [])
        , -- Frame + literal ~ concrete singleton with matching element.
          -- Canonical "one called-out element + frame variable" shape — the
          -- KEVM membership lemma family ('X in (REST |Set SetItem(Y:Int))').
          -- One syntactic match → commit; the frame variable binds to the
          -- (empty) leftover subject.
          test
            "frame + literal ~ concrete singleton"
            (kset [dvN 7] (Just (var "REST" setSort)))
            (kset [dvN 7] Nothing)
            (success [("REST", setSort, kset [] Nothing)])
        , -- Frame + variable element ~ concrete two-element set.  Multi-match
          -- ambiguity: 'Y' could bind to either 5 or 6, both sound but distinct.
          -- Sound matcher bails Indeterminate rather than picking arbitrarily
          -- (the design constraint that prevents n-way pairwise matching).
          test
            "frame + variable element ~ concrete two-element set (multi-match: stays Indeterminate)"
            (kset [var "Y" someSort] (Just (var "REST" setSort)))
            (kset [dvN 5, dvN 6] Nothing)
            (indet (kset [var "Y" someSort] (Just (var "REST" setSort))) (kset [dvN 5, dvN 6] Nothing))
        , -- Frame + literal ~ frame + same literal.  One syntactic match → commit;
          -- the smart constructor normalises @KSet _ [] (Just A)@ to @A@, so the
          -- frame variable 'REST' binds directly to the subject's frame 'A'.
          test
            "frame + literal ~ frame + same literal"
            (kset [dvN 7] (Just (var "REST" setSort)))
            (kset [dvN 7] (Just (var "A" setSort)))
            (success [("REST", setSort, var "A" setSort)])
        , -- Frame + variable element ~ frame + two distinct literal elements.
          -- The pattern variable 'X' could bind to 1 or 2 — multi-match — and
          -- the subject's own frame might hide further matches.  Bails
          -- Indeterminate.  (NB: a duplicate-literal subject like
          -- '[1, 1] (Just A)' would be deduplicated to '[1] (Just A)' by the
          -- 'KSet' smart constructor, so the genuine multi-match shape needs
          -- distinct literals.)
          test
            "frame + variable element ~ frame + two distinct literals (multi-match: stays Indeterminate)"
            (kset [var "X" someSort] (Just (var "S" setSort)))
            (kset [dvN 1, dvN 2] (Just (var "A" setSort)))
            ( indet
                (kset [var "X" someSort] (Just (var "S" setSort)))
                (kset [dvN 1, dvN 2] (Just (var "A" setSort)))
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

success :: [(VarName, Sort, Term)] -> MatchResult
success assocs =
    MatchSuccess $
        Map.fromList
            [ (Variable{variableSort, variableName}, term)
            | (variableName, variableSort, term) <- assocs
            ]

indet :: Term -> Term -> MatchResult
indet p s = MatchIndeterminate Map.empty (NE.singleton (p, s))
