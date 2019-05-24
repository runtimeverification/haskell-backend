require "harness.k"

module FUNCTIONS

  imports HARNESS
  imports BOOL
  imports INT

  rule <k> begin => next true </k>

  // `positive` is defined if its argument is positive.
  syntax Bool ::= positive(Int) [function]
  rule positive(M) => true
    requires M >Int 0

endmodule
