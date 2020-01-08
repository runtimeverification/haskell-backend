/*
 * If we have cycles, we can prove anything.  However, maybe we would rather
 * detect and report cycles, since the user probably did not intend to prove
 * everything.
 *
 */
module PATH
  import DOMAINS
  syntax S ::= "a" | "b" | "c"

  rule a => a
endmodule
