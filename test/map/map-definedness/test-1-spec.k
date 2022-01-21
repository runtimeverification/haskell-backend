requires "test.k"

module VERIFICATION
  imports TEST
endmodule

module TEST-1-SPEC
  imports VERIFICATION

  claim
    <k> add(X, 3) => end </k>
    <a> Y:Int |-> 2 M:Map => ?_ </a>

endmodule
