// Copyright (c) 2016-2018 K Team. All Rights Reserved.

requires "smc.k"

module DOUBLE-SUM-SPEC
  imports SMC


claim
    <k>
      while (!(p <= 0)) {
        sum = sum + p + p + p + p + p + p;
        p = p + -1;
      }
    =>
      .K
    ...</k>
  <mem>
      n   |-> _:Int
      p   |-> (P:Int => 0)
      sum |-> (S:Int => S +Int (3 *Int ((P +Int 1) *Int P)))
  </mem>
  <stack> .ValStack </stack>
requires P >=Int 0

claim
    <k>
      while (!(n <= 0)) {
        p = n;
        n = n + -1;
        while (!(p <= 0)) {
            sum = sum + p + p + p + p + p + p;
            p = p + -1;
        }
      }
    =>
      .K
    ...</k>
  <mem>
      n   |-> (N:Int => 0)
      p   |-> 0
      sum |-> (S:Int => S +Int (N *Int (N +Int 1) *Int (N +Int 2)))
  </mem>
  <stack> .ValStack </stack>
requires N >=Int 0

claim
    <k>
      int n, p, sum;
      n = N:Int;
      sum = 0;
      p = 0;
      while (!(n <= 0)) {
        p = n;
        n = n + -1;
        while (!(p <= 0)) {
            sum = sum + p + p + p + p + p + p;
            p = p + -1;
        }
      }
    =>
      .K
    </k>
  <mem>
    .Map
  =>
      n   |-> 0
      p   |-> 0
      sum |-> (N *Int (N +Int 1) *Int (N +Int 2))
  </mem>
  <stack> .ValStack </stack>
requires N >=Int 0

endmodule
