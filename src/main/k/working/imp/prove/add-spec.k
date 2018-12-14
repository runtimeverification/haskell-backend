/*
*/

module ADD-SPEC
  imports IMP

  syntax Id ::= "sum" [token]

  rule
    <k>
sum = 1 + 1;
=> .K
    </k>
    <state>sum |-> 0 => sum |-> 2</state>

endmodule
