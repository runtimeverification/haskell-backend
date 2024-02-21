/*
 * If we have cycles, we can prove anything.  However, maybe we would rather
 * detect and report cycles, since the user probably did not intend to prove
 * everything.
 *
 */
module PATH
  imports BOOL
  imports INT
  syntax S ::= "a" | "b" | "c"

  rule a => a
endmodule
