requires "test.k"

module TEST-1-SPEC
  imports TEST

  claim
    <k> add(X, 3) => end </k>
    <a> Y:Int |-> 2 M:Map => ?_ </a>

endmodule
