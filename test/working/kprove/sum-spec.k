// Copyright (c) 2016-2018 K Team. All Rights Reserved.
requires "verification.k"


module SUM-INVARIANT
  imports VERIFICATION

rule
    <k>
     loop
    =>
     .K
    ...</k>
  <state>
      n   |-> (N:Int => 0)
      sum |-> (S:Int => S +Int ((N +Int 1) *Int N))
  </state>
requires N >=Int 0

endmodule


module SUM-SPEC
  imports SUM-INVARIANT

rule
    <k>
      main(N:Int)
    =>
      .K
    </k>
  <state>
    .Map
  =>
      n   |-> 0
      sum |-> ((N +Int 1) *Int N)
  </state>
requires N >=Int 0
endmodule
