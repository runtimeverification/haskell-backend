/*
*/

module VERIFICATION
  imports IMP

  syntax Id ::= "sum" [token]
endmodule


module ADD-SPEC
  imports VERIFICATION
  imports IMP

  rule
    <k>
sum = 1 + 1;
=> .K
    </k>
    <state>sum |-> 0 => sum |-> 2</state>

endmodule
