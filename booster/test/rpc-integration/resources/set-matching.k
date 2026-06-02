// Standalone reproducer for booster's non-empty Set / AC `_|Set_` matching gap.
//
// `matchSets` (booster/library/Booster/Pattern/Match.hs, ~L674-L677) returns
// `MatchIndeterminate` for any non-empty set on either side; the five
// production set-membership / dedup simplification rules below (verbatim
// from KEVM `lemmas/lemmas.k:40-60`) therefore never fire in booster-dev
// even when the subject is fully concrete or has a single called-out
// element + frame variable.
//
// The `runLemma`/`doneLemma` harness lets a `simplify` RPC request carry
// the lemma's LHS pattern as its subject; if the rule fires the result is
// `doneLemma(<RHS>)`, otherwise it stays `runLemma(<LHS>)`.
//
// A future fix should:
//   * decide concrete-vs-concrete sets by multiset equality,
//   * commit on a single 'SetItem(literal)' + frame variable when the
//     subject has exactly one syntactically compatible element,
//   * keep returning `MatchIndeterminate` on multi-match ambiguity.

module SET-MATCHING
  imports INT
  imports BOOL
  imports SET

  syntax StepSort ::= Bool | Set
  syntax KItem   ::= runLemma  ( StepSort ) [symbol(runLemma)]
                   | doneLemma ( StepSort ) [symbol(doneLemma)]

  rule <k> runLemma(T) => doneLemma(T) ... </k>

  // The KEVM set-membership / dedup simplification rules — verbatim shape.
  // Each LHS carries either a non-empty `SetItem(...)` set or the AC `_|Set_`
  // symbol, so booster's matcher bails Indeterminate on every one of them.

  rule X in (SetItem(Y) _   ) => true      requires           X  ==Int Y   [simplification, preserves-definedness]
  rule X in (SetItem(Y) REST) => X in REST requires notBool ( X  ==Int Y ) [simplification, preserves-definedness]

  rule X:Int in (REST:Set |Set SetItem(Y:Int)) => true      requires           X  ==Int Y   [simplification, preserves-definedness]
  rule X:Int in (REST:Set |Set SetItem(Y:Int)) => X in REST requires notBool ( X  ==Int Y ) [simplification, preserves-definedness]

  rule S:Set |Set SetItem(X:Int) => S requires X in S [simplification, preserves-definedness]

  configuration <k> $PGM:KItem </k>

endmodule
