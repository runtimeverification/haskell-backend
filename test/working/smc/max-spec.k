/*
*/

module VERIFICATION
  imports SMC

  syntax Id ::= "a" [token]
  syntax Id ::= "b" [token]
  syntax Id ::= "max" [token]
endmodule


module MAX-SPEC
  imports VERIFICATION
  imports SMC

  rule
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
