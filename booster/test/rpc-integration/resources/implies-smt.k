// Minimal definition for exercising booster's `implies` check against
// integer / boolean obligations that need SMT discharge.
//
// The test claims send raw KORE `implies` requests whose antecedent and
// consequent share identical configurations (so the matcher returns
// MatchSuccess) but differ in their attached path-condition predicates.
// The interesting cases are the ones where the leftover consequent
// predicate is *implied* by the antecedent under linear-integer reasoning
// (e.g. `X <Int 1000` from `X <Int 100`), so an SMT-aware discharge
// step would close them as `valid : true`.
//
// The configuration is a single `<k>` cell containing an `Int` — enough
// to give us a kompiled definition with `_<Int_`, `andBool`, `true`, and
// the standard cell wrappers without any extra ceremony.

module IMPLIES-SMT
  imports INT
  imports BOOL

  configuration <k> $PGM:Int </k>

endmodule
