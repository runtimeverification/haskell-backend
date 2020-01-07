// Copyright (c) 2016-2018 K Team. All Rights Reserved.


module VERIFICATION
  imports SMC

// verification ids
  syntax Id ::= "n"     [token]
              | "p"     [token]
              | "sum"   [token]
endmodule

module DOUBLE-SUM-STACK-SPEC
  imports SMC
  imports VERIFICATION


rule
    <k>
      while (!(p <= 0)) {
        sum = sum + (p + (p + (p + (p + (p + p)))));
        p = p + -1;
      }
    =>
      .K
    ...</k>
  <mem>
      n   |-> N:Int
      p   |-> (P:Int => 0)
      sum |-> (S:Int => S +Int (3 *Int ((P +Int 1) *Int P)))
  </mem>
  <stack> VS:ValStack </stack>
requires P >=Int 0 andBool stackSize(VS) <=Int 1

rule
    <k>
      while (!(n <= 0)) {
        p = n;
        n = n + -1;
        while (!(p <= 0)) {
            sum = sum + (p + (p + (p + (p + (p + p)))));
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
  <stack> VS:ValStack </stack>
requires N >=Int 0 andBool stackSize(VS) <=Int 1

/*
rule
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
*/
endmodule
