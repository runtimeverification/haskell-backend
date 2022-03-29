requires "test.k"

module TEST-2-SPEC
  imports TEST

  claim
    <k> add(X, 3) => end </k>
    <a> 2 |-> 3 M N => ?_ </a>

endmodule
