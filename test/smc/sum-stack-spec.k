// Copyright (c) 2016-2018 K Team. All Rights Reserved.


module VERIFICATION
  imports SMC

// verification ids
  syntax Id ::= "n"     [token]
              | "sum"   [token]
endmodule


module SUM-STACK-SPEC
  imports SMC
  imports VERIFICATION


rule
    <k>
      while (!(n <= 0)) {
        sum = sum + (n + n);
        n = n + -1;
      }
    =>
      .K
    ...</k>
  <mem>
      n   |-> (N:Int => 0)
      sum |-> (S:Int => S +Int ((N +Int 1) *Int N))
  </mem>
  <stack>
     VS:ValStack
  </stack>
  requires N >=Int 0 andBool stackSize(VS) <=Int 5

rule
    <k>
      int n, sum;
      n = N:Int;
      sum = 0;
      while (!(n <= 0)) {
        sum = sum + (n + n);
        n = n + -1;
      }
    =>
      .K
    </k>
  <mem>
    .Map
  =>
      n   |-> 0
      sum |-> ((N +Int 1) *Int N)
  </mem>
  <stack>
     VS:ValStack
  </stack>
  requires N >=Int 0 andBool stackSize(VS) <=Int 5
endmodule
