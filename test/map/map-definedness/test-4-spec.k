module VERIFICATION
  imports TEST
endmodule

module TEST-4-SPEC
  imports VERIFICATION

  rule
    <k> add(f(X), f(3)) => end </k>
    <a> 2 |-> 3 M => ?_ </a>

endmodule
