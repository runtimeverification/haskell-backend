// Minimal definition pinning the partial-substitution pruning of indeterminate
// matches in booster's 'applyRule'.
//
// Shape mirrors the motivating KEVM '#addr [OP] / wordStack' case:
//   * 'Two' (higher priority): LHS structurally deconstructs the second arg
//     (cons-of-cons), so matching it against a symbolic 'MyList' free variable
//     is indeterminate. The first arg is a Bool-sorted rule variable B that
//     cleanly binds into the partial substitution. 'requires B' is then
//     trivially evaluable under the partial sub.
//   * 'Catch' (lower priority): unconditional catch-all.
//
// With subject 'step(false, S:MyList)':
//   - Pre-fix: 'Two' aborts with RuleApplicationUnclear (indeterminate match).
//     The catch-all is never tried; the whole step aborts at depth 0.
//   - Post-fix: 'Two's MatchIndeterminate carries the partial sub {B -> false}.
//     'checkRequires' substitutes 'requires B' to 'requires false', which is
//     immediately FalseBool. 'Two' is pruned via returnNotApplied, 'Catch' is
//     tried next and fires, leaving 'doneCatch'.

module ESCALATE-PARTIAL-MATCH
  imports BOOL

  syntax Op ::= "foo" | "bar"

  syntax MyList ::= "nilL" | cons(Op, MyList)

  syntax State ::= step(Bool, MyList) | "doneTwo" | "doneCatch"

  rule [Two]:   <k> step(B, cons(_, cons(_, _))) => doneTwo ... </k>
    requires B [priority(50)]

  rule [Catch]: <k> step(_B, _LIST) => doneCatch ... </k> [priority(60)]

  configuration <k> $PGM:State </k>

endmodule
