{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause

Exhaustive dispatch-class test for the matcher: for every combination of
match mode ('Rewrite', 'Eval', 'Implies') and top-level term-constructor
pair, pin whether 'matchTerms' succeeds ('S'), fails decisively ('F'), or
defers as indeterminate ('I').

The point of this module is the 'grid' tables: they are an explicit,
reviewable statement of the matcher's dispatch policy over all
3 x 9 x 9 = 243 (mode, pattern, subject) combinations. Any change to the
@match1@ table in "Booster.Pattern.Match" shows up here as a grid-cell
diff, making the behavioural surface of a matcher refactor visible at a
glance. The companion fine-grained tests (Test.Booster.Pattern.MatchEval
and friends) pin exact substitutions, failure reasons, and remainders;
this module only pins the result /class/.

Each term constructor is represented by one canonical pattern term and
one canonical subject term (see 'kinds'), chosen so that every cell's
class is deterministic and, where the dispatch descends into contents
(same-category pairs, \and decomposition, variable binding), the
contents resolve cleanly:

* variables in canonical patterns are distinct from one another and from
  subject variables (so the shared-variable check never interferes);
* the canonical \and subject has two /equal/ halves, so a variable
  pattern binds against both without conflict;
* same-category canonical pairs match successfully (the diagonal is 'S'),
  except where the mode itself defers (e.g. function-vs-function outside
  'Eval');
* the canonical variable pattern has sort @someSort@, so collection
  subjects (whose sorts are unrelated to @someSort@) exercise the
  sort-mismatch failure of @matchVar@.
-}
module Test.Booster.Pattern.MatchDispatch (
    test_match_dispatch,
) where

import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Pattern.Match
import Test.Booster.Fixture
import Test.Booster.Pattern.InternalCollections (emptyList, emptySet)

-- | Result class of a 'MatchResult'.
data Outcome
    = -- | 'MatchSuccess'
      S
    | -- | 'MatchFailed' (decisive)
      F
    | -- | 'MatchIndeterminate' (deferred)
      I
    deriving stock (Eq, Show)

classOf :: MatchResult -> Outcome
classOf MatchSuccess{} = S
classOf MatchFailed{} = F
classOf MatchIndeterminate{} = I

{- | One canonical (name, pattern term, subject term) triple per term
constructor, in the fixed axis order used by 'grid':

@AndTerm, DomainValue, Injection, KMap, KList, KSet, ConsApplication, FunctionApplication, Var@
-}
kinds :: [(String, Term, Term)]
kinds =
    [ ("AndTerm", AndTerm (var "P1" someSort) (var "P2" someSort), AndTerm subjCons subjCons)
    , ("DomainValue", dv someSort "d", dv someSort "d")
    ,
        ( "Injection"
        , Injection aSubsort someSort (var "PI" aSubsort)
        , Injection aSubsort someSort (dv aSubsort "i")
        )
    , ("KMap", emptyKMap, emptyKMap)
    , ("KList", emptyList, emptyList)
    , ("KSet", emptySet, emptySet)
    , ("ConsApplication", app con1 [var "PC" someSort], subjCons)
    , ("FunctionApplication", app f1 [var "PF" someSort], app f1 [dv someSort "f"])
    , ("Var", var "PX" someSort, var "SY" someSort)
    ]
  where
    subjCons = app con1 [dv someSort "c"]

{- | Expected dispatch class per mode: rows are the pattern constructor,
columns the subject constructor, both in 'kinds' order.

Read e.g. @grid Eval !! 7 !! 1 == F@ as: in 'Eval' mode, a
'FunctionApplication' pattern against a 'DomainValue' subject fails
decisively.
-}
grid :: MatchType -> [[Outcome]]
grid Rewrite =
    --  And DV  Inj Map List Set Cons Fun Var
    [ [S, S, S, F, F, F, S, S, S] -- AndTerm
    , [F, S, F, F, F, F, F, I, I] -- DomainValue
    , [F, F, S, F, F, F, F, I, I] -- Injection
    , [F, F, F, S, F, F, F, I, I] -- KMap
    , [F, F, F, F, S, F, F, I, I] -- KList
    , [F, F, F, F, F, S, F, I, I] -- KSet
    , [S, F, F, F, F, F, S, I, I] -- ConsApplication
    , [I, I, I, I, I, I, I, I, I] -- FunctionApplication
    , [S, S, S, F, F, F, S, S, S] -- Var
    ]
grid Eval =
    --  And DV  Inj Map List Set Cons Fun Var
    [ [I, S, S, F, F, F, S, S, I] -- AndTerm
    , [I, S, F, F, F, F, F, I, I] -- DomainValue
    , [I, F, S, I, I, I, F, I, I] -- Injection
    , [I, F, I, S, F, F, F, I, I] -- KMap
    , [I, F, I, F, S, F, F, I, I] -- KList
    , [I, F, I, F, F, S, F, I, I] -- KSet
    , [I, F, F, F, F, F, S, I, I] -- ConsApplication
    , [I, I, I, I, I, I, I, S, I] -- FunctionApplication
    , [I, S, S, F, F, F, S, S, S] -- Var
    ]
grid Implies =
    --  And DV  Inj Map List Set Cons Fun Var
    [ [S, S, S, F, F, F, S, S, S] -- AndTerm
    , [F, S, F, F, F, F, F, I, I] -- DomainValue
    , [F, F, S, F, F, F, F, I, I] -- Injection
    , [F, F, F, S, F, F, F, I, I] -- KMap
    , [F, F, F, F, S, F, F, I, I] -- KList
    , [F, F, F, F, F, S, F, I, I] -- KSet
    , [S, F, F, F, F, F, S, I, I] -- ConsApplication
    , [I, I, I, I, I, I, I, I, I] -- FunctionApplication
    , [S, S, S, F, F, F, S, S, S] -- Var
    ]

test_match_dispatch :: TestTree
test_match_dispatch =
    testGroup
        "matchTerms dispatch classes (mode x pattern x subject)"
        [ testGroup
            modeName
            [ testCase (patName <> " vs " <> subjName) $
                classOf (matchTerms mode testDefinition patTerm subjTerm) @?= expected
            | ((patName, patTerm, _), row) <- zip kinds (grid mode)
            , ((subjName, _, subjTerm), expected) <- zip kinds row
            ]
        | (modeName, mode) <- [("Rewrite", Rewrite), ("Eval", Eval), ("Implies", Implies)]
        ]
