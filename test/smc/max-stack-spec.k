requires "smc.k"
/*
*/

module MAX-STACK-SPEC
  imports SMC

  claim
    <k>
      if (a <= b)
      { max = b; }
      else
      { max = a; }
      => .K
    </k>
    <mem>
      a |-> A:Int
      b |-> B:Int
      max |-> (_ => A)
    </mem>
    <stack> S:ValStack </stack>
    requires A >Int B andBool stackSize(S) <=Int 6

endmodule
