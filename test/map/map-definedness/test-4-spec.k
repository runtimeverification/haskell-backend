requires "test.k"

module TEST-4-SPEC
  imports TEST

  claim
    <k> add(f(X), f(3)) => end </k>
    <a> 2 |-> 3 M => ?_ </a>

endmodule
