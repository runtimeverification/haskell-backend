// Copyright (c) 2016-2018 K Team. All Rights Reserved.
requires "smc.k"

module SUM-SPEC
  imports SMC


claim
    <k>
      while (!(n <= 0)) {
        sum = sum + n + n;
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
     .ValStack => .ValStack
  </stack>
  requires N >=Int 0

claim
    <k>
      int n, sum;
      n = N:Int;
      sum = 0;
      while (!(n <= 0)) {
        sum = sum + n + n;
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
     .ValStack
  </stack>
  requires N >=Int 0
endmodule
