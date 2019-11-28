module UNIFICATION-SYNTAX
  imports DOMAINS-SYNTAX

  syntax BExp  ::= Bool
                 | "!" BExp
endmodule

module UNIFICATION
  imports UNIFICATION-SYNTAX

  rule ! (notBool T) => T

endmodule
