module VERIFICATION
  imports TEST
endmodule

module TEST-4-SPEC
  imports VERIFICATION

  rule
    <k> add(f(X), 3) => end </k>
    <a> M => ?_ </a>

endmodule
