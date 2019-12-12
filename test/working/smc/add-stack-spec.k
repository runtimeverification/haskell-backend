/*
*/

module VERIFICATION
  imports SMC

  syntax Id ::= "sum" [token]
endmodule


module ADD-STACK-SPEC
  imports VERIFICATION
  imports SMC

  rule
    <k>
sum = 1 + 1;
=> .K
    </k>
    <mem> sum |-> (I:Int => 2) </mem>
    <stack> S:ValStack </stack>
    requires stackSize(S) <=Int 6

endmodule
