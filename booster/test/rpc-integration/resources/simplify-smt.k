module SIMPLIFY-SMT-SYNTAX
  imports INT
  imports BOOL
  imports STRING

// testing SMT solver use during equation application

  syntax Thing ::= unevaluated ( Int, Int ) [function, symbol("unevaluated")]
                 | evaluated ( String )     [symbol("evaluated")]
endmodule

module SIMPLIFY-SMT
  imports INT
  imports BOOL
  imports SIMPLIFY-SMT-SYNTAX

  // contradicting requires clauses: unclear in isolation, false when checked together
  rule [bad-requires]:
    unevaluated(A, B) => evaluated("contradicting requires clause")
      requires A *Int B <=Int 0 andBool A <Int B andBool B <Int A // should never apply
      [priority(10), preserves-definedness]
      // unclear without SMT solver, aborting function evaluation)

  // Should apply with the right path conditions about A and B.
  rule [good-requires]:
    unevaluated(A, B) => evaluated("A and B have the same sign and are not zero")
      requires 0 <Int A *Int B
      [priority(20), preserves-definedness]

  // contradicting ensures clauses: unclear in isolation, false when checked together
  rule [bad-ensures]:
    unevaluated(A, B) => evaluated("contradicting ensures clause")
      ensures A <Int B andBool B <Int A // should terminate the evaluation
      [priority(30), preserves-definedness]
      // would be added to the path condition without SMT solver

endmodule
