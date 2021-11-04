requires "path.k"

module VERIFICATION
  imports PATH

endmodule

module ALL-PATH-PARTIAL-SPEC
  imports VERIFICATION
  imports PATH

  // This should not be provable both one-path and all-path.
  // because it does not hold for X = c
  claim <k> partial(X:S) => end </k> [all-path]

endmodule
