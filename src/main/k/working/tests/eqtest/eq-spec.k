/*
*/

module VERIFICATION
  imports EQTEST

  syntax Int ::= f (Int) [function]

  rule f (X:Int) => X

endmodule


module EQ-SPEC
  imports VERIFICATION
  imports EQTEST

  rule
    <k>
    f (X:Int /Int X) => 1
    </k>

endmodule
