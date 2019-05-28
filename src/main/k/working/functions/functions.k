require "harness.k"

module FUNCTIONS

  imports HARNESS
  imports DOMAINS

  rule <k> begin => next true </k>

  // `positive` is defined if its argument is positive.
  syntax Bool ::= positive(Int) [function]
  rule positive(M) => true
    requires M >Int 0

  syntax ConsList ::= ".ConsList" | KItem ":" ConsList

  // `length` is inductively defined.
  syntax Int ::= length(ConsList) [function, functional, inductive(1)]
  rule length(.ConsList) => 0
  rule length(_ : TAIL) => 1 +Int length(TAIL)

endmodule
