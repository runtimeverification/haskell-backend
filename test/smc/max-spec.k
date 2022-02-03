requires "smc.k"
/*
*/

module MAX-SPEC
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
    <stack> .ValStack </stack>
    requires A >Int B

endmodule
