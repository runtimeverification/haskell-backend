requires "harness.k"

module FUNCTIONS

  imports HARNESS
  imports INT
  imports BOOL

  rule <k> begin => next true </k>

  // `positive` is defined if its argument is positive.
  syntax Bool ::= positive(Int) [function]
  rule positive(M) => true
    requires M >Int 0

  syntax ConsList ::= ".ConsList" | KItem ":" ConsList

  // `length` is inductively defined.
  syntax Int ::= length(ConsList) [function, total]
  rule length(.ConsList) => 0
  rule length(_ : TAIL) => 1 +Int length(TAIL)

endmodule
