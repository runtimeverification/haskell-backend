requires "test.k"

module VERIFICATION
  imports TEST
endmodule

module TEST-3-SPEC
  imports VERIFICATION

  claim
    <k> add(X, 3) => end </k>
    <a> M => ?_ </a>

endmodule
