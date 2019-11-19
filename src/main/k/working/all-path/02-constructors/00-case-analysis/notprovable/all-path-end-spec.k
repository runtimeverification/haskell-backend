module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-END-SPEC
  imports VERIFICATION
  imports PATH

  // This should not be provable both one-path and all-path.
  // because it does not hold for X = c
  rule <k> g(X:S) => end </k> [all-path]

endmodule
