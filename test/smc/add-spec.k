requires "smc.k"
/*
*/

module VERIFICATION
  imports SMC

  syntax Id ::= "sum" [token]
endmodule


module ADD-SPEC
  imports VERIFICATION
  imports SMC

  claim
    <k>
sum = 1 + 1;
=> .K
    </k>
    <mem> sum |-> (_:Int => 2) </mem>
    <stack> .ValStack </stack>

endmodule
