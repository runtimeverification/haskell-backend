/*
*/

requires "imp.k"

module ADD-SPEC
  imports IMP

  claim
    <k>
sum = 1 + 1;
=> .K
    </k>
    <state>sum |-> 0 => sum |-> 2</state>

endmodule
