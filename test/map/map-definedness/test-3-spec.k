requires "test.k"

module TEST-3-SPEC
  imports TEST

  claim
    <k> add(X, 3) => end </k>
    <a> M => ?_ </a>

endmodule
