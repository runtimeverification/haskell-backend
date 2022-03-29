requires "smc.k"
/*
*/

module ADD-SPEC
  imports SMC

  claim
    <k>
sum = 1 + 1;
=> .K
    </k>
    <mem> sum |-> (_:Int => 2) </mem>
    <stack> .ValStack </stack>

endmodule
