requires "test.k"

module SUM-SPEC
  imports TEST

  claim  <k> loop(N:Int) => .K ...</k>
        <counter> C:Int => ?_ </counter>
        <sum> S:Int => ?S:Int </sum>
    requires
      N >=Int 0
    ensures
      ?S ==Int S +Int N *Int C +Int (N -Int 1) *Int N /Int 2
endmodule
