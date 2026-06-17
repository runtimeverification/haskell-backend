# test-implies-smt

Exercises booster's `implies` endpoint on integer/boolean obligations that need SMT discharge.

Each test sends a raw KORE `implies` request whose antecedent and consequent share an identical `<k>` configuration — so the matcher returns `MatchSuccess` — but differ in their attached path-condition predicates.
The leftover consequent predicate is then simplified under the antecedent and any residue is SMT-closed, so the verdict turns on linear-integer reasoning rather than syntactic matching.
The definition (`resources/implies-smt.k`) is just `configuration <k> $PGM:Int </k>` over `INT`/`BOOL`.

The four cases cover each arm of the discharge logic, and `002` deliberately diverges between the two engines: booster's SMT cannot refute the obligation and returns `indeterminate` (the signal for a recover-mode client to escalate), whereas kore decides it.

| test                  | antecedent ⟹ consequent           | booster `status` | kore `status` | arm exercised                                    |
|-----------------------|------------------------------------|------------------|---------------|--------------------------------------------------|
| 001-bound-weakening   | `X <Int 100` ⟹ `X <Int 1000`      | valid            | valid         | SMT discharges a weaker bound (`IsValid`)        |
| 002-does-not-imply    | `X <Int 100` ⟹ `X <Int 10`        | indeterminate    | invalid       | SMT cannot refute → `IsUnknown` → escalate       |
| 003-vacuous-antecedent| contradictory antecedent ⟹ _any_   | valid            | valid         | unsat ground truth (`InconsistentGroundTruth`)   |
| 004-address-bound     | address-range bounds ⟹ weaker bound| valid            | valid         | conjunctive bound discharge over 2^160 / 2^256   |

Responses are checked against `response-<test>.json` (kore / default server) and `response-<test>.booster-dev` (booster-dev server).
