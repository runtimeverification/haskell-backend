requires "smc.k"

/*
*/

module ADD-STACK-SPEC
  imports SMC

  claim
    <k>
sum = 1 + 1;
=> .K
    </k>
    <mem> sum |-> (_:Int => 2) </mem>
    <stack> S:ValStack </stack>
    requires stackSize(S) <=Int 6

endmodule
